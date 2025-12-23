use anchor_lang::prelude::*;

#[account]
pub struct AuctionState {
    pub authority: Pubkey,

    // SPL mints
    pub token_mint: Pubkey,
    pub currency_mint: Pubkey,

    // Program vaults (SPL token accounts) holding token supply + collected currency
    pub token_vault: Pubkey,
    pub currency_vault: Pubkey,

    // PDA bump for signing vault transfers
    pub vault_authority_bump: u8,

    // Tick spacing in price units (currency atomic units per ONE token).
    // Enforces max_price granularity to avoid tick fragmentation.
    pub tick_spacing: u128,

    pub total_supply: u128,
    // SPL token decimals (used to derive `one_token = 10^decimals`)
    pub token_decimals: u8,
    // 10^token_decimals
    pub one_token: u128,
    pub start_time: i64,
    pub end_time: i64,

    // Config
    pub floor_price: u128,
    pub min_bid_amount: u128,
    pub required_currency_raised: u128,

    // Dynamic State
    // Rates are stored with constants::PRECISION scaling:
    // supply_rate: token_atomic_units * PRECISION / second
    // current_flow_rate: currency_atomic_units * PRECISION / second
    pub supply_rate: u128,
    pub current_flow_rate: u128,
    // currency_atomic_units per ONE token (10^decimals), rounded up
    pub current_clearing_price: u128,

    pub last_update_time: i64,

    // The Global Accumulator: Integral( one_token / (PRECISION * P(t)) dt )
    // Used to calculate how many token-atomic-units a unit of *scaled* flow has earned.
    pub acc_tokens_per_share: u128,

    // Total tokens released so far
    pub cumulative_supply_released: u128,
    // Total currency raised so far
    pub cumulative_demand_raised: u128,
}

impl AuctionState {
    pub const LEN: usize = 8
        + 32
        + 32
        + 32
        + 32
        + 32
        + 1
        + 16
        + 16
        + 1
        + 16
        + 8
        + 8
        + 16
        + 16
        + 16
        + 16
        + 16
        + 16
        + 8
        + 16
        + 16
        + 16;
}

#[account]
pub struct TickState {
    pub price: u128,      // Key
    pub flow_delta: u128, // How much flow leaves if this tick is crossed

    // Crossing info
    pub crossed_at: i64,    // Timestamp when price went ABOVE this tick
    pub snapshot_acc: u128, // Global accumulator value at that moment

    pub bump: u8,
}

impl TickState {
    pub const LEN: usize = 8 + 16 + 16 + 8 + 16 + 1;
}

#[account]
pub struct BidState {
    pub auction: Pubkey,
    pub owner: Pubkey,
    pub amount: u128,
    pub max_price: u128,
    pub flow_rate: u128,

    pub creation_time: i64,
    pub last_acc_snapshot: u128, // Accumulator value when bid was placed

    // Settlement
    pub tokens_filled: u128,
    pub refund_amount: u128,

    // Claim guard (do not use tokens/refund as a sentinel; both can be 0 due to rounding)
    pub claim_time: i64,
}

impl BidState {
    pub const LEN: usize = 8 + 32 + 32 + 16 + 16 + 16 + 8 + 16 + 16 + 16 + 8;
}
