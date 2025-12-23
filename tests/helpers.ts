import { Program } from "@coral-xyz/anchor";
import { PublicKey } from "@solana/web3.js";

// BidState layout (Anchor account discriminator is 8 bytes):
// 0..8   discriminator
// 8..40  auction pubkey
// 40..72 owner pubkey
const BIDSTATE_AUCTION_OFFSET = 8;
const BIDSTATE_OWNER_OFFSET = 8 + 32;

export type UserBidAccount<TBidState> = {
  publicKey: PublicKey;
  account: TBidState;
};

/**
 * Lists a user's bids for a specific auction using efficient RPC memcmp filters.
 *
 * Requires on-chain `BidState` to include `auction: Pubkey` then `owner: Pubkey`.
 */
export async function fetchUserBidsForAuction<TBidState>(
  program: Program<any>,
  auction: PublicKey,
  owner: PublicKey
): Promise<UserBidAccount<TBidState>[]> {
  // Anchor will:
  // - add the discriminator filter automatically
  // - decode accounts into `TBidState`
  const rows = await (program.account as any).bidState.all([
    {
      memcmp: {
        offset: BIDSTATE_AUCTION_OFFSET,
        bytes: auction.toBase58(),
      },
    },
    {
      memcmp: {
        offset: BIDSTATE_OWNER_OFFSET,
        bytes: owner.toBase58(),
      },
    },
  ]);

  return rows as UserBidAccount<TBidState>[];
}
