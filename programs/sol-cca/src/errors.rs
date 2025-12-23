use anchor_lang::prelude::*;

#[error_code]
pub enum CCAError {
    #[msg("Auction is not active")]
    AuctionNotActive,
    #[msg("Bid amount is too small")]
    BidTooSmall,
    #[msg("Price is below current clearing price")]
    PriceBelowClearing,
    #[msg("Auction has already ended")]
    AuctionEnded,
    #[msg("Auction is still active")]
    AuctionStillActive,
    #[msg("Bid has already been claimed")]
    AlreadyClaimed,
    #[msg("Invalid tick account")]
    InvalidTick,
    #[msg("Not the owner of the bid")]
    NotOwner,
    #[msg("Invalid auction duration")]
    InvalidAuctionDuration,

    #[msg("Invalid token decimals")]
    InvalidTokenDecimals,

    #[msg("Invalid tick spacing")]
    InvalidTickSpacing,

    #[msg("Max price not aligned to tick spacing")]
    InvalidTickPrice,

    #[msg("Settlement amount exceeds u64")]
    AmountTooLarge,

    #[msg("Math overflow")]
    MathOverflow,

    #[msg("Tick accounts must be sorted by price ascending")]
    InvalidTickOrder,

    #[msg("Invalid bid id")]
    InvalidBidId,

    #[msg("Bid does not belong to this auction")]
    InvalidBidAuction,
}
