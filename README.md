# sol-cca

Continuous Clearing Auction (CCA) implementation on Solana using Anchor.

This repo contains:
- An on-chain program in [programs/sol-cca](programs/sol-cca)
- TypeScript tests in [tests](tests)

## Overview

The auction sells a fixed token supply over a time window. Bids contribute a constant flow rate (currency per second) until the auction ends or until the bid is outbid (via tick crossing).

Key ideas:
- **Clearing price** is derived from the current global flow vs. supply rate.
- **Accumulator (`acc_tokens_per_share`)** tracks the time integral used to settle token allocations.
- **Ticks** represent price levels; if the clearing price crosses above a tick, all flow at that tick is removed.

## Build

Prerequisites:
- Rust toolchain
- Solana CLI
- Anchor CLI
- Node.js + Yarn

Commands:
- `anchor build`
- `cargo test`

## Program ID

The program ID is configured in [Anchor.toml](Anchor.toml) and must match `declare_id!` in the program.

## Instructions

### `initialize`

Initializes an `AuctionState` account.

Args:
- `total_supply: u64`
- `token_decimals: u8`
- `start_time: i64`
- `end_time: i64`
- `floor_price: u64`
- `min_bid_amount: u64`
- `required_currency_raised: u64`

### `submit_bid`

Places a bid and registers its flow into the tick of `max_price`.

Args:
- `bid_nonce: u64` (user-provided; enables concurrent multi-bids without reading chain state)
- `amount: u64`
- `max_price: u128`

Notes:
- A user can place multiple bids as long as `bid_nonce` is unique per user+auction.
- Tick crossing requires passing relevant tick accounts via `remaining_accounts` (sorted by price ascending).

### `claim`

Settles a bid after the auction ends (or after it was outbid, once the auction is graduated/ended).

Args:
- `bid_nonce: u64`

## PDA Derivations

### Bid PDA

Bid accounts are uniquely derived per user and per `bid_nonce`:

Seeds:
- `"bid"`
- `auction_pubkey`
- `user_pubkey`
- `bid_nonce` as little-endian `u64` (8 bytes)

### Tick PDA

Tick accounts are derived by price (stored as `u128`):

Seeds:
- `"tick"`
- `auction_pubkey`
- `max_price` as little-endian `u128` (16 bytes)

## Listing a User's Bids for an Auction (RPC filters)

`BidState` stores both:
- `auction: Pubkey`
- `owner: Pubkey`

This allows efficient RPC filtering (memcmp) by auction+owner.

In tests, see:
- [tests/helpers.ts](tests/helpers.ts): `fetchUserBidsForAuction(program, auction, owner)`

## Tests

Install deps:
- `yarn install`

Format check:
- `yarn run lint`

Run TS tests:
- `anchor test`

If you want to run `ts-mocha` directly, you need to set the Anchor env vars (e.g. `ANCHOR_PROVIDER_URL`, `ANCHOR_WALLET`).