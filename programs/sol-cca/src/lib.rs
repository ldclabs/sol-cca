//! # Continuous Clearing Auction
//!
//! This module implements a Continuous Clearing Auction (CCA) mechanism for token sales on Solana using Anchor.
//!
//! References: https://docs.uniswap.org/contracts/liquidity-launchpad/CCA
//!
use anchor_lang::prelude::*;
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token_interface::{self, Mint, TokenAccount, TokenInterface, TransferChecked};
use std::cmp::min;

pub mod errors;
pub mod state;

use errors::*;
use state::*;

declare_id!("HJZnotK691hkN8XM5RuzPyk6tZnreFPRFMKrMGux6Pz1");

pub mod constants {
    pub const PRECISION: u128 = 1_000_000_000; // 1e9
    pub const ACC_PRECISION: u128 = 1_000_000_000_000; // 1e12
}

pub mod seeds {
    pub const VAULT_AUTHORITY: &[u8] = b"vault_authority";
    pub const TOKEN_VAULT: &[u8] = b"token_vault";
    pub const CURRENCY_VAULT: &[u8] = b"currency_vault";
}

fn ceil_div(n: u128, d: u128) -> Result<u128> {
    require!(d != 0, CCAError::MathOverflow);
    let n = n
        .checked_add(d - 1)
        .ok_or_else(|| error!(CCAError::MathOverflow))?;
    Ok(n / d)
}

fn align_up(value: u128, spacing: u128) -> Result<u128> {
    require!(spacing != 0, CCAError::InvalidTickSpacing);
    Ok(ceil_div(value, spacing)? * spacing)
}

#[program]
pub mod solana_cca {
    use super::*;

    /// Estimate the clearing price after adding `amount`, and the minimum recommended `max_price`.
    ///
    /// This instruction does not mutate on-chain state. Clients should call it via simulation
    /// and parse logs.
    pub fn estimate_max_price(ctx: Context<EstimateMaxPrice>, amount: u64) -> Result<()> {
        let auction = &ctx.accounts.auction;
        let clock = Clock::get()?;
        let now = clock.unix_timestamp;

        let effective_now = std::cmp::max(now, auction.start_time);
        require!(now < auction.end_time, CCAError::AuctionNotActive);

        let mut virtual_auction: AuctionState = auction.as_ref().clone().into_inner();
        update_auction_accumulators(&mut virtual_auction, effective_now)?;

        let remaining_time = (virtual_auction.end_time - effective_now) as u128;
        require!(remaining_time > 0, CCAError::AuctionEnded);

        let flow_rate = (amount as u128)
            .checked_mul(constants::PRECISION)
            .ok_or_else(|| error!(CCAError::MathOverflow))?
            / remaining_time;

        // Minimum max_price lower bound (same rule as submit_bid).
        let tick_spacing_u128 = virtual_auction.tick_spacing as u128;
        let mut min_required_price = virtual_auction.current_clearing_price as u128;
        if virtual_auction.supply_rate > 0 {
            let delta_num = flow_rate
                .checked_mul(virtual_auction.one_token as u128)
                .ok_or_else(|| error!(CCAError::MathOverflow))?;
            let price_delta = ceil_div(delta_num, virtual_auction.supply_rate)?;
            min_required_price = min_required_price
                .checked_add(price_delta)
                .ok_or_else(|| error!(CCAError::MathOverflow))?;
        }
        let min_required_price = align_up(min_required_price, tick_spacing_u128)?;

        // Estimated new clearing price (before any tick crossings / outbids are processed).
        let est_price = if virtual_auction.supply_rate > 0 {
            let total_flow = virtual_auction
                .current_flow_rate
                .checked_add(flow_rate)
                .ok_or_else(|| error!(CCAError::MathOverflow))?;
            let numerator = total_flow
                .checked_mul(virtual_auction.one_token as u128)
                .ok_or_else(|| error!(CCAError::MathOverflow))?;
            let raw_p = ceil_div(numerator, virtual_auction.supply_rate)?;
            std::cmp::max(raw_p, virtual_auction.floor_price as u128)
        } else {
            virtual_auction.floor_price as u128
        };

        require!(est_price <= u64::MAX as u128, CCAError::MathOverflow);
        require!(
            min_required_price <= u64::MAX as u128,
            CCAError::MathOverflow
        );

        msg!(
            "estimate_max_price: amount={}, flow_rate={}, est_clearing_price={}, min_max_price={}",
            amount,
            flow_rate,
            est_price as u64,
            min_required_price as u64
        );

        Ok(())
    }

    /// Initialize the auction
    pub fn initialize(
        ctx: Context<Initialize>,
        total_supply: u64,
        token_decimals: u8,
        start_time: i64,
        end_time: i64,
        floor_price: u64,
        tick_spacing: u64,
        min_bid_amount: u64,
        required_currency_raised: u64,
        tokens_recipient: Pubkey,
        funds_recipient: Pubkey,
    ) -> Result<()> {
        require!(end_time > start_time, CCAError::InvalidAuctionDuration);

        require!(
            ctx.accounts.token_mint.decimals == token_decimals,
            CCAError::InvalidTokenDecimals
        );

        let auction = &mut ctx.accounts.auction;
        auction.authority = ctx.accounts.authority.key();

        auction.token_mint = ctx.accounts.token_mint.key();
        auction.currency_mint = ctx.accounts.currency_mint.key();
        auction.token_vault = ctx.accounts.token_vault.key();
        auction.currency_vault = ctx.accounts.currency_vault.key();
        auction.tokens_recipient = tokens_recipient;
        auction.funds_recipient = funds_recipient;
        auction.vault_authority_bump = ctx.bumps.vault_authority;

        auction.total_supply = total_supply;
        auction.token_decimals = token_decimals;
        // If we store `one_token` as u64, cap decimals to avoid overflow.
        require!(token_decimals <= 19, CCAError::InvalidTokenDecimals);
        auction.one_token = 10u64
            .checked_pow(token_decimals as u32)
            .ok_or_else(|| error!(CCAError::MathOverflow))?;

        auction.start_time = start_time;
        auction.end_time = end_time;
        auction.floor_price = floor_price;
        require!(tick_spacing > 0, CCAError::InvalidTickSpacing);
        auction.tick_spacing = tick_spacing;
        auction.min_bid_amount = min_bid_amount;
        auction.required_currency_raised = required_currency_raised;

        // Initial supply rate = Total / Duration
        let duration = (end_time - start_time) as u128;
        auction.supply_rate = ((auction.total_supply as u128) * constants::PRECISION) / duration;

        auction.last_update_time = start_time;
        auction.current_clearing_price = floor_price;

        auction.swept_currency = false;
        auction.swept_token = false;

        Ok(())
    }

    /// Place a bid
    /// This is the most complex instruction. It updates global flow AND handles "Tick Crossing".
    ///
    /// Why `remaining_accounts`?
    /// If this bid pushes the price up past existing Ticks, we need to pass those Tick accounts
    /// to "cross" them (remove their flow). This is the "Crank" logic embedded in the bid.
    pub fn submit_bid<'info>(
        ctx: Context<'_, '_, 'info, 'info, SubmitBid<'info>>,
        _bid_nonce: u64,
        amount: u64,
        max_price: u64,
    ) -> Result<()> {
        let auction = &mut ctx.accounts.auction;
        let bid = &mut ctx.accounts.bid;
        let tick = &mut ctx.accounts.tick; // The tick corresponding to user's max_price
        let clock = Clock::get()?;
        let now = clock.unix_timestamp;

        // Allow users to submit bids before `start_time` to avoid contention.
        // Funds are escrowed immediately, but the bid only becomes economically active at `start_time`.
        let effective_now = std::cmp::max(now, auction.start_time);

        require!(now < auction.end_time, CCAError::AuctionNotActive);
        require!(amount >= auction.min_bid_amount, CCAError::BidTooSmall);
        require!(
            max_price >= auction.current_clearing_price,
            CCAError::PriceBelowClearing
        );

        // Enforce tick granularity to avoid tick fragmentation.
        require!(auction.tick_spacing > 0, CCAError::InvalidTickSpacing);
        require!(
            max_price % auction.tick_spacing == 0,
            CCAError::InvalidTickPrice
        );

        // 0. Move user's currency into program vault (escrow)
        token_interface::transfer_checked(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                TransferChecked {
                    from: ctx.accounts.user_currency.to_account_info(),
                    mint: ctx.accounts.currency_mint.to_account_info(),
                    to: ctx.accounts.currency_vault.to_account_info(),
                    authority: ctx.accounts.user.to_account_info(),
                },
            ),
            amount,
            ctx.accounts.currency_mint.decimals,
        )?;

        // 1. Update Auction State (Accumulators) to effective_now
        // If the user bids early, we do NOT accrue anything before start_time.
        update_auction_accumulators(auction, effective_now)?;

        // 2. Calculate User Flow
        let remaining_time = (auction.end_time - effective_now) as u128;
        require!(remaining_time > 0, CCAError::AuctionEnded);

        // flow = amount / remaining_time
        let flow_rate = (amount as u128)
            .checked_mul(constants::PRECISION)
            .ok_or_else(|| error!(CCAError::MathOverflow))?
            / remaining_time;

        // 2.1 Enforce a lower bound for max_price.
        // Rationale: prevent a bidder from using a huge amount with a slightly-above-clearing max_price
        // to temporarily spike the price and crank other ticks out, while getting fully refunded by
        // immediately self-outbidding.
        let tick_spacing_u128 = auction.tick_spacing as u128;
        let mut min_required_price = auction.current_clearing_price as u128;
        if auction.supply_rate > 0 {
            // Upper bound on the new clearing price contributed by this bid's flow alone:
            // P' <= P + ceil(flow_rate * one_token / supply_rate)
            let delta_num = flow_rate
                .checked_mul(auction.one_token as u128)
                .ok_or_else(|| error!(CCAError::MathOverflow))?;
            let price_delta = ceil_div(delta_num, auction.supply_rate)?;
            min_required_price = min_required_price
                .checked_add(price_delta)
                .ok_or_else(|| error!(CCAError::MathOverflow))?;
        }
        // Respect tick granularity.
        let min_required_price = align_up(min_required_price, tick_spacing_u128)?;
        require!(
            min_required_price <= u64::MAX as u128,
            CCAError::MathOverflow
        );
        require!(
            max_price as u128 >= min_required_price,
            CCAError::MaxPriceTooLow
        );

        // 3. Update Bid State
        bid.auction = auction.key();
        bid.owner = ctx.accounts.user.key();
        bid.amount = amount;
        bid.max_price = max_price;
        bid.flow_rate = flow_rate;
        bid.last_acc_snapshot = auction.acc_tokens_per_share; // Snapshot at entry
                                                              // `creation_time` is the wall-clock submission time (can be < start_time).
                                                              // Economic activation is handled in `claim` via effective_start_time.
        bid.creation_time = now;
        bid.claim_time = 0;

        // 4. Register Flow into the Tick (Wait to be outbid)
        // Note: The tick PDA is derived from [auction_pubkey, max_price]
        if tick.flow_delta == 0 {
            // Init tick if new
            tick.price = max_price;
            tick.bump = ctx.bumps.tick;
        }
        tick.flow_delta = tick
            .flow_delta
            .checked_add(flow_rate)
            .ok_or_else(|| error!(CCAError::MathOverflow))?;

        // 5. Update Global Flow (Increase Demand)
        auction.current_flow_rate = auction
            .current_flow_rate
            .checked_add(flow_rate)
            .ok_or_else(|| error!(CCAError::MathOverflow))?;

        // 6. Recalculate Price & Handle Outbids (The "Crank")
        // First, update clearing price upwards based on the new flow.
        // Then, if the higher price crosses existing ticks, we "crank" them out.
        if auction.supply_rate > 0 {
            let numerator = auction
                .current_flow_rate
                .checked_mul(auction.one_token as u128)
                .ok_or_else(|| error!(CCAError::MathOverflow))?;
            let raw_p = ceil_div(numerator, auction.supply_rate)?;
            let floor_p = auction.floor_price as u128;
            let p_u128 = std::cmp::max(raw_p, floor_p);
            require!(p_u128 <= u64::MAX as u128, CCAError::MathOverflow);
            auction.current_clearing_price = p_u128 as u64;
        } else {
            auction.current_clearing_price = auction.floor_price;
        }

        // Check if new flow pushes price > lowest active ticks
        // If the bid was placed early, any crossing is recorded at start_time.
        process_tick_crossings(auction, ctx.remaining_accounts, effective_now)?;

        Ok(())
    }

    /// Claim tokens / Refund
    /// User calls this after auction ends OR if they suspect they are outbid.
    pub fn claim(ctx: Context<Claim>, _bid_nonce: u64) -> Result<()> {
        let auction = &mut ctx.accounts.auction;
        let bid = &mut ctx.accounts.bid;
        let tick = &ctx.accounts.tick; // User's max_price tick
        let clock = Clock::get()?;
        let now = clock.unix_timestamp;

        // If the bid was submitted before the auction started, it becomes economically active at `start_time`.
        let effective_start_time = std::cmp::max(bid.creation_time, auction.start_time);

        // Sync global state first
        update_auction_accumulators(auction, now)?;

        require!(bid.claim_time == 0, CCAError::AlreadyClaimed);

        let mut tokens_filled = 0u128;
        let refund_amount: u128;

        let is_graduated = auction.cumulative_demand_raised >= auction.required_currency_raised;

        // Logic: active or outbid?
        // We look at the TICK state.
        // If Tick.crossed_at != 0, it means this price level was breached.

        if tick.crossed_at > 0 {
            // --- SCENARIO: OUTBID ---
            // User was valid from `bid.creation_time` until `tick.crossed_at`

            if is_graduated || now >= auction.end_time {
                if is_graduated {
                    // If the price level was crossed before this bid became active,
                    // the user was never in-range.
                    if tick.crossed_at <= effective_start_time {
                        refund_amount = bid.amount as u128;
                        tokens_filled = 0;
                    } else {
                        // 1. Tokens: Integrate from entry snapshot to crossing
                        if tick.snapshot_acc > bid.last_acc_snapshot {
                            let acc_delta = tick.snapshot_acc - bid.last_acc_snapshot;
                            tokens_filled = bid
                                .flow_rate
                                .checked_mul(acc_delta)
                                .ok_or_else(|| error!(CCAError::MathOverflow))?
                                / constants::ACC_PRECISION;
                        }

                        // 2. Refund: Unspent money
                        let duration_active = (tick.crossed_at - effective_start_time) as u128;
                        let spent = (bid.flow_rate * duration_active) / constants::PRECISION;
                        refund_amount = (bid.amount as u128).saturating_sub(spent);
                    }
                } else {
                    // Auction ended and failed
                    refund_amount = bid.amount as u128;
                    tokens_filled = 0;
                }
            } else {
                // Auction still active and not yet graduated.
                return err!(CCAError::AuctionStillActive);
            }
        } else {
            // --- SCENARIO: ACTIVE (or Auction Ended comfortably) ---

            if now >= auction.end_time {
                if is_graduated {
                    // Auction ended, user survived
                    let acc_delta = auction.acc_tokens_per_share - bid.last_acc_snapshot;
                    tokens_filled = bid
                        .flow_rate
                        .checked_mul(acc_delta)
                        .ok_or_else(|| error!(CCAError::MathOverflow))?
                        / constants::ACC_PRECISION;

                    // Refund dust
                    let duration_active = (auction.end_time - effective_start_time) as u128;
                    let spent = (bid.flow_rate * duration_active) / constants::PRECISION;
                    refund_amount = (bid.amount as u128).saturating_sub(spent);
                } else {
                    // Auction ended and failed
                    refund_amount = bid.amount as u128;
                    tokens_filled = 0;
                }
            } else {
                return err!(CCAError::AuctionStillActive);
            }
        }

        // Update state to prevent re-entrancy/double claim
        require!(tokens_filled <= u64::MAX as u128, CCAError::AmountTooLarge);
        require!(refund_amount <= u64::MAX as u128, CCAError::AmountTooLarge);
        bid.tokens_filled = tokens_filled as u64;
        bid.refund_amount = refund_amount as u64;
        bid.claim_time = now;

        // --- Settlement transfers ---
        // Vault authority PDA signs transfers out of vaults.
        let auction_key = auction.key();
        let signer_seeds: &[&[u8]] = &[
            seeds::VAULT_AUTHORITY,
            auction_key.as_ref(),
            &[auction.vault_authority_bump],
        ];

        if bid.tokens_filled > 0 {
            token_interface::transfer_checked(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    TransferChecked {
                        from: ctx.accounts.token_vault.to_account_info(),
                        mint: ctx.accounts.token_mint.to_account_info(),
                        to: ctx.accounts.user_token.to_account_info(),
                        authority: ctx.accounts.vault_authority.to_account_info(),
                    },
                    &[signer_seeds],
                ),
                bid.tokens_filled,
                ctx.accounts.token_mint.decimals,
            )?;
        }

        if bid.refund_amount > 0 {
            token_interface::transfer_checked(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    TransferChecked {
                        from: ctx.accounts.currency_vault.to_account_info(),
                        mint: ctx.accounts.currency_mint.to_account_info(),
                        to: ctx.accounts.user_currency.to_account_info(),
                        authority: ctx.accounts.vault_authority.to_account_info(),
                    },
                    &[signer_seeds],
                ),
                bid.refund_amount,
                ctx.accounts.currency_mint.decimals,
            )?;
        }

        msg!(
            "Claimed: Tokens={}, Refund={}",
            bid.tokens_filled,
            bid.refund_amount
        );

        Ok(())
    }

    /// Sweep raised currency to `funds_recipient` after the auction ends and graduates.
    ///
    /// IMPORTANT: only sweeps the *spent* amount (`cumulative_demand_raised`).
    /// The remaining currency in the vault is needed for refunds for bids that were outbid
    /// or otherwise not fully spent.
    pub fn sweep_currency(ctx: Context<SweepCurrency>) -> Result<()> {
        let auction = &mut ctx.accounts.auction;
        let clock = Clock::get()?;
        let now = clock.unix_timestamp;

        require!(now >= auction.end_time, CCAError::AuctionStillActive);

        // Finalize accumulators (caps to end_time internally).
        update_auction_accumulators(auction, now)?;

        require!(
            auction.cumulative_demand_raised >= auction.required_currency_raised,
            CCAError::AuctionNotGraduated
        );
        require!(!auction.swept_currency, CCAError::AlreadySwept);

        let amount_to_sweep = auction.cumulative_demand_raised;
        if amount_to_sweep == 0 {
            auction.swept_currency = true;
            return Ok(());
        }

        // Ensure we don't drain funds needed for refunds.
        require!(
            ctx.accounts.currency_vault.amount >= amount_to_sweep,
            CCAError::MathOverflow
        );

        let auction_key = auction.key();
        let signer_seeds: &[&[u8]] = &[
            seeds::VAULT_AUTHORITY,
            auction_key.as_ref(),
            &[auction.vault_authority_bump],
        ];

        token_interface::transfer_checked(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                TransferChecked {
                    from: ctx.accounts.currency_vault.to_account_info(),
                    mint: ctx.accounts.currency_mint.to_account_info(),
                    to: ctx.accounts.funds_recipient.to_account_info(),
                    authority: ctx.accounts.vault_authority.to_account_info(),
                },
                &[signer_seeds],
            ),
            amount_to_sweep,
            ctx.accounts.currency_mint.decimals,
        )?;

        auction.swept_currency = true;
        Ok(())
    }

    /// Sweep *unsold* tokens to `tokens_recipient` after the auction ends and graduates.
    ///
    /// IMPORTANT: only transfers `total_supply - cumulative_supply_released`.
    /// This ensures the vault keeps enough tokens for users who haven't claimed yet.
    pub fn sweep_token(ctx: Context<SweepToken>) -> Result<()> {
        let auction = &mut ctx.accounts.auction;
        let clock = Clock::get()?;
        let now = clock.unix_timestamp;

        require!(now >= auction.end_time, CCAError::AuctionStillActive);

        // Finalize accumulators (caps to end_time internally).
        update_auction_accumulators(auction, now)?;

        require!(
            auction.cumulative_demand_raised >= auction.required_currency_raised,
            CCAError::AuctionNotGraduated
        );
        require!(!auction.swept_token, CCAError::AlreadySwept);

        require!(
            auction.total_supply >= auction.cumulative_supply_released,
            CCAError::MathOverflow
        );
        let unsold = auction.total_supply - auction.cumulative_supply_released;
        if unsold == 0 {
            auction.swept_token = true;
            return Ok(());
        }

        // Safety check: token_vault must always retain claimable tokens.
        require!(
            ctx.accounts.token_vault.amount >= unsold,
            CCAError::MathOverflow
        );

        let auction_key = auction.key();
        let signer_seeds: &[&[u8]] = &[
            seeds::VAULT_AUTHORITY,
            auction_key.as_ref(),
            &[auction.vault_authority_bump],
        ];

        token_interface::transfer_checked(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                TransferChecked {
                    from: ctx.accounts.token_vault.to_account_info(),
                    mint: ctx.accounts.token_mint.to_account_info(),
                    to: ctx.accounts.tokens_recipient.to_account_info(),
                    authority: ctx.accounts.vault_authority.to_account_info(),
                },
                &[signer_seeds],
            ),
            unsold,
            ctx.accounts.token_mint.decimals,
        )?;

        auction.swept_token = true;
        Ok(())
    }
}

// --- Helper Functions ---

/// Updates the integral accumulator (Sigma 1/P dt)
fn update_auction_accumulators(auction: &mut AuctionState, now: i64) -> Result<()> {
    if now <= auction.last_update_time {
        return Ok(());
    }

    // Cap at end_time
    let effective_now = min(now, auction.end_time);
    let dt = (effective_now - auction.last_update_time) as u128;

    if dt == 0 {
        return Ok(());
    }

    // D(t) Delta: Based on current flow rate
    let demand_delta = auction
        .current_flow_rate
        .checked_mul(dt)
        .ok_or_else(|| error!(CCAError::MathOverflow))?
        / constants::PRECISION;
    let new_demand = (auction.cumulative_demand_raised as u128)
        .checked_add(demand_delta)
        .ok_or_else(|| error!(CCAError::MathOverflow))?;
    require!(new_demand <= u64::MAX as u128, CCAError::MathOverflow);
    auction.cumulative_demand_raised = new_demand as u64;

    // Calc Clearing Price
    // Price = (Flow / SupplyRate) * one_token
    let price_u128 = if auction.supply_rate > 0 {
        let numerator = auction
            .current_flow_rate
            .checked_mul(auction.one_token as u128)
            .ok_or_else(|| error!(CCAError::MathOverflow))?;
        let raw_p = ceil_div(numerator, auction.supply_rate)?;
        std::cmp::max(raw_p, auction.floor_price as u128)
    } else {
        auction.floor_price as u128
    };

    require!(price_u128 <= u64::MAX as u128, CCAError::MathOverflow);
    let price: u64 = price_u128 as u64;
    auction.current_clearing_price = price;

    // Update Accumulator: Acc += dt / Price
    if price > 0 {
        let price_u128 = price as u128;
        // acc_delta = dt * ACC_PRECISION * one_token / (PRECISION * price)
        let num = (dt)
            .checked_mul(constants::ACC_PRECISION)
            .and_then(|v| v.checked_mul(auction.one_token as u128))
            .ok_or_else(|| error!(CCAError::MathOverflow))?;
        let denom = constants::PRECISION
            .checked_mul(price_u128)
            .ok_or_else(|| error!(CCAError::MathOverflow))?;
        let acc_delta = num / denom;
        auction.acc_tokens_per_share = auction
            .acc_tokens_per_share
            .checked_add(acc_delta)
            .ok_or_else(|| error!(CCAError::MathOverflow))?;

        // Update released tokens (token-atomic units):
        // released = current_flow_rate * acc_delta / ACC_PRECISION
        let released = auction
            .current_flow_rate
            .checked_mul(acc_delta)
            .ok_or_else(|| error!(CCAError::MathOverflow))?
            / constants::ACC_PRECISION;
        let new_released = (auction.cumulative_supply_released as u128)
            .checked_add(released)
            .ok_or_else(|| error!(CCAError::MathOverflow))?;
        require!(new_released <= u64::MAX as u128, CCAError::MathOverflow);
        auction.cumulative_supply_released = new_released as u64;
    }

    // Update time
    auction.last_update_time = effective_now;

    // Recalibrate Supply Rate (Linear release)
    // R = RemainingSupply / RemainingTime
    let time_left = (auction.end_time - effective_now) as u128;
    if time_left > 0 {
        let remaining_supply = auction
            .total_supply
            .saturating_sub(auction.cumulative_supply_released);
        auction.supply_rate = ((remaining_supply as u128) * constants::PRECISION) / time_left;
    }

    Ok(())
}

/// The "Crank" logic.
/// Iterates through provided Tick accounts. If Price > Tick.Price, we "cross" it.
fn process_tick_crossings<'info>(
    auction: &mut Account<'info, AuctionState>,
    remaining_accounts: &'info [AccountInfo<'info>],
    now: i64,
) -> Result<()> {
    // We expect remaining_accounts to be Tick PDAs, sorted by price ascending
    // User interface must provide the next 1-3 ticks that are in danger of being crossed.

    let mut current_p: u64 = auction.current_clearing_price;
    let mut last_price: u64 = 0;

    for acc in remaining_accounts.iter() {
        // Deserialize tick manually to save CU or use anchor approach
        let mut tick: Account<'info, TickState> = Account::try_from(acc)?;

        // Enforce ascending order to keep crossing logic correct
        require!(tick.price >= last_price, CCAError::InvalidTickOrder);
        last_price = tick.price;

        // Verify this tick belongs to this auction
        let (expected_pda, _bump) = Pubkey::find_program_address(
            &[b"tick", auction.key().as_ref(), &tick.price.to_le_bytes()],
            &crate::id(),
        );
        require!(expected_pda == *acc.key, CCAError::InvalidTick);

        // Safety check: is this tick relevant?
        // It must be: Tick.price < Current_Price AND Tick not already crossed
        if tick.crossed_at == 0 && tick.price < current_p {
            // --- CROSSING EVENT ---
            msg!("Crossing Tick Price: {}", tick.price);

            // 1. Snapshot the moment
            tick.crossed_at = now;
            tick.snapshot_acc = auction.acc_tokens_per_share;

            // 2. Remove Flow
            // These users are out. Their money stops pushing the price up.
            auction.current_flow_rate = auction.current_flow_rate.saturating_sub(tick.flow_delta);

            // 3. Recalculate Price with reduced flow
            if auction.supply_rate > 0 {
                let numerator = auction
                    .current_flow_rate
                    .checked_mul(auction.one_token as u128)
                    .ok_or_else(|| error!(CCAError::MathOverflow))?;
                let new_p = ceil_div(numerator, auction.supply_rate)?;
                let floor_p = auction.floor_price as u128;
                let p_u128 = std::cmp::max(new_p, floor_p);
                require!(p_u128 <= u64::MAX as u128, CCAError::MathOverflow);
                current_p = p_u128 as u64;
            } else {
                current_p = auction.floor_price;
            }

            // Write back
            tick.exit(&crate::id())?; // Save changes to account
        } else {
            // Since accounts should be sorted, if we don't cross this one, we won't cross higher ones
            break;
        }
    }

    auction.current_clearing_price = current_p;

    Ok(())
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(init, payer = authority, space = AuctionState::LEN)]
    pub auction: Box<Account<'info, AuctionState>>,
    #[account(mut)]
    pub authority: Signer<'info>,

    #[account(mint::token_program = token_program)]
    pub token_mint: InterfaceAccount<'info, Mint>,
    #[account(mint::token_program = token_program)]
    pub currency_mint: InterfaceAccount<'info, Mint>,

    /// CHECK: PDA that owns the vault token accounts
    #[account(
        seeds = [seeds::VAULT_AUTHORITY, auction.key().as_ref()],
        bump
    )]
    pub vault_authority: UncheckedAccount<'info>,

    #[account(
        init,
        payer = authority,
        seeds = [seeds::TOKEN_VAULT, auction.key().as_ref()],
        bump,
        token::mint = token_mint,
        token::authority = vault_authority,
        token::token_program = token_program
    )]
    pub token_vault: Box<InterfaceAccount<'info, TokenAccount>>,

    #[account(
        init,
        payer = authority,
        seeds = [seeds::CURRENCY_VAULT, auction.key().as_ref()],
        bump,
        token::mint = currency_mint,
        token::authority = vault_authority,
        token::token_program = token_program
    )]
    pub currency_vault: Box<InterfaceAccount<'info, TokenAccount>>,

    pub token_program: Interface<'info, TokenInterface>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct EstimateMaxPrice<'info> {
    pub auction: Box<Account<'info, AuctionState>>,
}

#[derive(Accounts)]
pub struct SweepCurrency<'info> {
    #[account(mut)]
    pub auction: Box<Account<'info, AuctionState>>,

    /// CHECK: PDA that owns the vault token accounts
    #[account(
        seeds = [seeds::VAULT_AUTHORITY, auction.key().as_ref()],
        bump = auction.vault_authority_bump
    )]
    pub vault_authority: UncheckedAccount<'info>,

    #[account(
        mut,
        seeds = [seeds::CURRENCY_VAULT, auction.key().as_ref()],
        bump,
        constraint = currency_vault.mint == auction.currency_mint,
        constraint = currency_vault.owner == vault_authority.key()
    )]
    pub currency_vault: Box<InterfaceAccount<'info, TokenAccount>>,

    #[account(
        constraint = currency_mint.key() == auction.currency_mint,
        mint::token_program = token_program
    )]
    pub currency_mint: InterfaceAccount<'info, Mint>,

    #[account(
        mut,
        constraint = funds_recipient.key() == auction.funds_recipient,
        constraint = funds_recipient.mint == auction.currency_mint
    )]
    pub funds_recipient: Box<InterfaceAccount<'info, TokenAccount>>,

    pub token_program: Interface<'info, TokenInterface>,
}

#[derive(Accounts)]
pub struct SweepToken<'info> {
    #[account(mut)]
    pub auction: Box<Account<'info, AuctionState>>,

    /// CHECK: PDA that owns the vault token accounts
    #[account(
        seeds = [seeds::VAULT_AUTHORITY, auction.key().as_ref()],
        bump = auction.vault_authority_bump
    )]
    pub vault_authority: UncheckedAccount<'info>,

    #[account(
        mut,
        seeds = [seeds::TOKEN_VAULT, auction.key().as_ref()],
        bump,
        constraint = token_vault.mint == auction.token_mint,
        constraint = token_vault.owner == vault_authority.key()
    )]
    pub token_vault: Box<InterfaceAccount<'info, TokenAccount>>,

    #[account(
        constraint = token_mint.key() == auction.token_mint,
        mint::token_program = token_program
    )]
    pub token_mint: InterfaceAccount<'info, Mint>,

    #[account(
        mut,
        constraint = tokens_recipient.key() == auction.tokens_recipient,
        constraint = tokens_recipient.mint == auction.token_mint
    )]
    pub tokens_recipient: Box<InterfaceAccount<'info, TokenAccount>>,

    pub token_program: Interface<'info, TokenInterface>,
}

#[derive(Accounts)]
#[instruction(bid_nonce: u64, amount: u64, max_price: u64)]
pub struct SubmitBid<'info> {
    #[account(mut)]
    pub auction: Box<Account<'info, AuctionState>>,
    #[account(
        init,
        payer = user,
        space = BidState::LEN,
        seeds = [b"bid", auction.key().as_ref(), user.key().as_ref(), &bid_nonce.to_le_bytes()],
        bump
    )]
    pub bid: Box<Account<'info, BidState>>,
    #[account(
        init_if_needed,
        payer = user,
        space = TickState::LEN,
        seeds = [b"tick", auction.key().as_ref(), &max_price.to_le_bytes()],
        bump
    )]
    pub tick: Box<Account<'info, TickState>>,
    #[account(mut)]
    pub user: Signer<'info>,

    #[account(
        constraint = currency_mint.key() == auction.currency_mint,
        mint::token_program = token_program
    )]
    pub currency_mint: InterfaceAccount<'info, Mint>,

    #[account(
        mut,
        constraint = user_currency.owner == user.key(),
        constraint = user_currency.mint == auction.currency_mint
    )]
    pub user_currency: Box<InterfaceAccount<'info, TokenAccount>>,

    /// CHECK: PDA that owns the vault token accounts
    #[account(
        seeds = [seeds::VAULT_AUTHORITY, auction.key().as_ref()],
        bump = auction.vault_authority_bump
    )]
    pub vault_authority: UncheckedAccount<'info>,

    #[account(
        mut,
        seeds = [seeds::CURRENCY_VAULT, auction.key().as_ref()],
        bump,
        constraint = currency_vault.mint == auction.currency_mint,
        constraint = currency_vault.owner == vault_authority.key()
    )]
    pub currency_vault: Box<InterfaceAccount<'info, TokenAccount>>,

    pub token_program: Interface<'info, TokenInterface>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(bid_nonce: u64)]
pub struct Claim<'info> {
    #[account(mut)]
    pub auction: Box<Account<'info, AuctionState>>,
    #[account(
        mut,
        seeds = [b"bid", auction.key().as_ref(), user.key().as_ref(), &bid_nonce.to_le_bytes()],
        bump,
        constraint = bid.owner == user.key() @ CCAError::NotOwner,
        constraint = bid.auction == auction.key() @ CCAError::InvalidBidAuction
    )]
    pub bid: Box<Account<'info, BidState>>,
    #[account(
        seeds = [b"tick", auction.key().as_ref(), &bid.max_price.to_le_bytes()],
        bump = tick.bump
    )]
    pub tick: Box<Account<'info, TickState>>,
    #[account(mut)]
    pub user: Signer<'info>,

    #[account(
        constraint = token_mint.key() == auction.token_mint,
        mint::token_program = token_program
    )]
    pub token_mint: InterfaceAccount<'info, Mint>,
    #[account(
        constraint = currency_mint.key() == auction.currency_mint,
        mint::token_program = token_program
    )]
    pub currency_mint: InterfaceAccount<'info, Mint>,

    #[account(
        init_if_needed,
        payer = user,
        associated_token::mint = token_mint,
        associated_token::authority = user,
        associated_token::token_program = token_program
    )]
    pub user_token: Box<InterfaceAccount<'info, TokenAccount>>,

    #[account(
        mut,
        constraint = user_currency.owner == user.key(),
        constraint = user_currency.mint == auction.currency_mint
    )]
    pub user_currency: Box<InterfaceAccount<'info, TokenAccount>>,

    /// CHECK: PDA that owns the vault token accounts
    #[account(
        seeds = [seeds::VAULT_AUTHORITY, auction.key().as_ref()],
        bump = auction.vault_authority_bump
    )]
    pub vault_authority: UncheckedAccount<'info>,

    #[account(
        mut,
        seeds = [seeds::TOKEN_VAULT, auction.key().as_ref()],
        bump,
        constraint = token_vault.mint == auction.token_mint,
        constraint = token_vault.owner == vault_authority.key()
    )]
    pub token_vault: Box<InterfaceAccount<'info, TokenAccount>>,

    #[account(
        mut,
        seeds = [seeds::CURRENCY_VAULT, auction.key().as_ref()],
        bump,
        constraint = currency_vault.mint == auction.currency_mint,
        constraint = currency_vault.owner == vault_authority.key()
    )]
    pub currency_vault: Box<InterfaceAccount<'info, TokenAccount>>,

    pub token_program: Interface<'info, TokenInterface>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_test_auction() -> AuctionState {
        let token_decimals: u8 = 8;
        let one_token = 10u64.pow(token_decimals as u32);
        AuctionState {
            authority: Pubkey::default(),
            token_mint: Pubkey::default(),
            currency_mint: Pubkey::default(),
            token_vault: Pubkey::default(),
            currency_vault: Pubkey::default(),
            tokens_recipient: Pubkey::default(),
            funds_recipient: Pubkey::default(),
            vault_authority_bump: 0,
            tick_spacing: 1,
            total_supply: 1000 * 10u64.pow(8), // 1000 tokens, 8 decimals
            token_decimals,
            one_token,
            start_time: 1000,
            end_time: 11000,
            floor_price: 100,
            min_bid_amount: 1000,
            required_currency_raised: 100000,
            supply_rate: 0,
            current_flow_rate: 0,
            current_clearing_price: 100,
            last_update_time: 1000,
            acc_tokens_per_share: 0,
            cumulative_supply_released: 0,
            cumulative_demand_raised: 0,
            swept_currency: false,
            swept_token: false,
        }
    }

    #[test]
    fn test_basic_auction_flow() {
        let mut auction = get_test_auction();
        // Initial supply rate = Total / Duration = 1000e8 / 10000 = 10e6
        let duration = (auction.end_time - auction.start_time) as u128;
        auction.supply_rate = ((auction.total_supply as u128) * constants::PRECISION) / duration;
        assert_eq!(auction.supply_rate, 10_000_000 * constants::PRECISION);

        // 1. Update at start
        update_auction_accumulators(&mut auction, 1000).unwrap();
        assert_eq!(auction.acc_tokens_per_share, 0);

        // 2. Place Bid 1 at t=1000
        // amount = 50000, max_price = 500
        // remaining_time = 10000
        // flow_rate = 50000 * 1e9 / 10000 = 5 * 1e9
        let bid1_amount = 50000u128;
        let bid1_flow_rate = (bid1_amount * constants::PRECISION) / 10000;
        auction.current_flow_rate += bid1_flow_rate;
        assert_eq!(auction.current_flow_rate, 5 * constants::PRECISION);

        // 3. Update at t=6000
        update_auction_accumulators(&mut auction, 6000).unwrap();
        // dt = 5000
        // demand_delta = 5e9 * 5000 / 1e9 = 25000
        assert_eq!(auction.cumulative_demand_raised, 25000);
        // raw price = ceil(flow * one_token / supply_rate) = 50, but floor enforces 100
        assert_eq!(auction.current_clearing_price, 100);
        // acc_delta = dt * 1e12 * one_token / (1e9 * price)
        //          = 5000 * 1e12 * 1e8 / (1e9 * 100) = 5 * 1e12
        assert_eq!(auction.acc_tokens_per_share, 5 * constants::ACC_PRECISION);
        // released = flow * acc_delta / 1e12 = 5e9 * 5e12 / 1e12 = 25e9 = 250 tokens
        assert_eq!(auction.cumulative_supply_released, 250 * 10u64.pow(8));

        // 4. Place Bid 2 at t=6000
        // amount = 50000, max_price = 500
        // remaining_time = 5000
        // flow_rate = 50000 * 1e9 / 5000 = 10 * 1e9
        let bid2_amount = 50000u128;
        let bid2_flow_rate = (bid2_amount * constants::PRECISION) / 5000;
        auction.current_flow_rate += bid2_flow_rate;
        assert_eq!(auction.current_flow_rate, 15 * constants::PRECISION);

        // 5. Update at t=11000 (End)
        update_auction_accumulators(&mut auction, 11000).unwrap();
        // dt = 5000
        // demand_delta = 15e9 * 5000 / 1e9 = 75000
        // total demand = 25000 + 75000 = 100000
        assert_eq!(auction.cumulative_demand_raised, 100000);
        // price stays at floor (100) with these parameters
        assert_eq!(auction.current_clearing_price, 100);
    }

    #[test]
    fn test_auction_failure() {
        let mut auction = get_test_auction();
        let duration = (auction.end_time - auction.start_time) as u128;
        auction.supply_rate = ((auction.total_supply as u128) * constants::PRECISION) / duration;

        // Place a small bid
        let bid_amount = 10000u128;
        let bid_flow_rate = (bid_amount * constants::PRECISION) / 10000;
        auction.current_flow_rate += bid_flow_rate;

        // Update at end
        update_auction_accumulators(&mut auction, 11000).unwrap();

        // Total raised = 10000 < 100000
        assert!(auction.cumulative_demand_raised < auction.required_currency_raised);
        assert_eq!(auction.cumulative_demand_raised, 10000);
    }
}
