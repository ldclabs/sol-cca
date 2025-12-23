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
    // address to receive leftover tokens after auction ends
    pub tokens_recipient: Pubkey,
    // address to receive raised currency after auction ends
    pub funds_recipient: Pubkey,

    // PDA bump for signing vault transfers
    pub vault_authority_bump: u8,

    // Tick spacing in price units (currency atomic units per ONE token).
    // Enforces max_price granularity to avoid tick fragmentation.
    pub tick_spacing: u64,

    pub total_supply: u64,
    // SPL token decimals (used to derive `one_token = 10^decimals`)
    pub token_decimals: u8,
    // 10^token_decimals
    pub one_token: u64,
    pub start_time: i64,
    pub end_time: i64,

    // Config
    pub floor_price: u64,
    pub min_bid_amount: u64,
    pub required_currency_raised: u64,

    // Dynamic State
    // Rates are stored with constants::PRECISION scaling:
    // supply_rate: token_atomic_units * PRECISION / second
    // current_flow_rate: currency_atomic_units * PRECISION / second
    pub supply_rate: u128,
    pub current_flow_rate: u128,
    // currency_atomic_units per ONE token (10^decimals), rounded up
    pub current_clearing_price: u64,

    pub last_update_time: i64,

    // The Global Accumulator: Integral( one_token / (PRECISION * P(t)) dt )
    // Used to calculate how many token-atomic-units a unit of *scaled* flow has earned.
    pub acc_tokens_per_share: u128,

    // Total tokens released so far
    pub cumulative_supply_released: u64,
    // Total currency raised so far
    pub cumulative_demand_raised: u64,

    // Sweep guards
    pub swept_currency: bool,
    pub swept_token: bool,
}

impl AuctionState {
    pub const LEN: usize = 8
        + 32 // authority
        + 32 // token_mint
        + 32 // currency_mint
        + 32 // token_vault
        + 32 // currency_vault
        + 32 // tokens_recipient
        + 32 // funds_recipient
        + 1 // vault_authority_bump
        + 8 // tick_spacing
        + 8 // total_supply
        + 1 // token_decimals
        + 8 // one_token
        + 8 // start_time
        + 8 // end_time
        + 8 // floor_price
        + 8 // min_bid_amount
        + 8 // required_currency_raised
        + 16 // supply_rate
        + 16 // current_flow_rate
        + 8 // current_clearing_price
        + 8 // last_update_time
        + 16 // acc_tokens_per_share
        + 8 // cumulative_supply_released
        + 8 // cumulative_demand_raised
        + 1 // swept_currency
        + 1; // swept_token
}

#[account]
pub struct TickState {
    pub price: u64,       // Key
    pub flow_delta: u128, // How much flow leaves if this tick is crossed

    // Crossing info
    pub crossed_at: i64,    // Timestamp when price went ABOVE this tick
    pub snapshot_acc: u128, // Global accumulator value at that moment

    pub bump: u8,
}

impl TickState {
    pub const LEN: usize = 8 + 8 + 16 + 8 + 16 + 1;
}

#[account]
pub struct BidState {
    pub auction: Pubkey,
    pub owner: Pubkey,
    pub amount: u64,
    pub max_price: u64,
    pub flow_rate: u128,

    pub creation_time: i64,
    pub last_acc_snapshot: u128, // Accumulator value when bid was placed

    // Settlement
    pub tokens_filled: u64,
    pub refund_amount: u64,

    // Claim guard (do not use tokens/refund as a sentinel; both can be 0 due to rounding)
    pub claim_time: i64,
}

impl BidState {
    pub const LEN: usize = 8 + 32 + 32 + 8 + 8 + 16 + 8 + 16 + 8 + 8 + 8;
}
