import * as anchor from "@coral-xyz/anchor";
import { Program } from "@coral-xyz/anchor";
import { SolanaCca } from "../target/types/solana_cca";
import { expect } from "chai";
import { PublicKey, Keypair, SystemProgram } from "@solana/web3.js";
import { BN } from "bn.js";
import { fetchUserBidsForAuction } from "./helpers";
import {
  TOKEN_PROGRAM_ID,
  TOKEN_2022_PROGRAM_ID,
  ASSOCIATED_TOKEN_PROGRAM_ID,
  createMint,
  getAssociatedTokenAddress,
  getOrCreateAssociatedTokenAccount,
  getAccount,
  mintTo,
  transfer,
} from "@solana/spl-token";

describe("sol-cca", () => {
  const provider = process.env.ANCHOR_PROVIDER_URL
    ? anchor.AnchorProvider.env()
    : anchor.AnchorProvider.local();
  anchor.setProvider(provider);

  const program = anchor.workspace.SolanaCca as Program<SolanaCca>;

  const PRECISION = new BN(1_000_000_000);
  const ACC_PRECISION = new BN(1_000_000_000_000);

  let auctionKeypair = Keypair.generate();
  let authority = provider.wallet.publicKey;

  const payer = (provider.wallet as any).payer as Keypair;

  const getBidPda = (auction: PublicKey, user: PublicKey, bidNonce: anchor.BN) => {
    return PublicKey.findProgramAddressSync(
      [
        Buffer.from("bid"),
        auction.toBuffer(),
        user.toBuffer(),
        bidNonce.toArrayLike(Buffer, "le", 8),
      ],
      program.programId
    )[0];
  };

  const getTickPda = (auction: PublicKey, price: anchor.BN) => {
    return PublicKey.findProgramAddressSync(
      [
        Buffer.from("tick"),
        auction.toBuffer(),
        price.toArrayLike(Buffer, "le", 8),
      ],
      program.programId
    )[0];
  };

  const getVaultAuthorityPda = (auction: PublicKey) => {
    return PublicKey.findProgramAddressSync(
      [Buffer.from("vault_authority"), auction.toBuffer()],
      program.programId
    )[0];
  };

  const getTokenVaultPda = (auction: PublicKey) => {
    return PublicKey.findProgramAddressSync(
      [Buffer.from("token_vault"), auction.toBuffer()],
      program.programId
    )[0];
  };

  const getCurrencyVaultPda = (auction: PublicKey) => {
    return PublicKey.findProgramAddressSync(
      [Buffer.from("currency_vault"), auction.toBuffer()],
      program.programId
    )[0];
  };

  it("Basic Auction Flow", async () => {
    const startTime = Math.floor(Date.now() / 1000) + 2;
    const endTime = startTime + 6;
    const totalSupply = new BN(1000_000_000); // 10 tokens with 8 decimals
    const tokenDecimals = 8;
    const floorPrice = new BN(100);
    const tickSpacing = new BN(10);
    const minBidAmount = new BN(1000);
    const requiredCurrencyRaised = new BN(1);

    const tokenMint = await createMint(
      provider.connection,
      payer,
      authority,
      null,
      tokenDecimals
    );
    const currencyMint = await createMint(
      provider.connection,
      payer,
      authority,
      null,
      6
    );

    const vaultAuthorityPda = getVaultAuthorityPda(auctionKeypair.publicKey);
    const tokenVaultPda = getTokenVaultPda(auctionKeypair.publicKey);
    const currencyVaultPda = getCurrencyVaultPda(auctionKeypair.publicKey);

    const authorityTokenAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      tokenMint,
      authority
    );
    const authorityCurrencyAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      currencyMint,
      authority
    );
    await mintTo(
      provider.connection,
      payer,
      tokenMint,
      authorityTokenAta.address,
      payer,
      BigInt(totalSupply.toString())
    );

    await program.methods
      .initialize(
        totalSupply,
        tokenDecimals,
        new BN(startTime),
        new BN(endTime),
        floorPrice,
        tickSpacing,
        minBidAmount,
        requiredCurrencyRaised,
        authorityTokenAta.address,
        authorityCurrencyAta.address
      )
      .accounts({
        auction: auctionKeypair.publicKey,
        authority: authority,
        tokenMint,
        currencyMint,
        vaultAuthority: vaultAuthorityPda,
        tokenVault: tokenVaultPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([auctionKeypair])
      .rpc();

    // Fund token vault so claims can succeed
    await transfer(
      provider.connection,
      payer,
      authorityTokenAta.address,
      tokenVaultPda,
      payer,
      BigInt(totalSupply.toString())
    );

    let auction = await program.account.auctionState.fetch(
      auctionKeypair.publicKey
    );
    expect(auction.totalSupply.toString()).to.equal(totalSupply.toString());
    expect(auction.floorPrice.toString()).to.equal(floorPrice.toString());

    // Wait for auction to start
    while (Math.floor(Date.now() / 1000) < startTime) {
      await new Promise((resolve) => setTimeout(resolve, 1000));
    }

    const user1 = Keypair.generate();
    const bidAmount1 = new BN(50000);
    const maxPrice1 = new BN(500); // aligned to tickSpacing=10

    // Airdrop to user1
    const signature = await provider.connection.requestAirdrop(
      user1.publicKey,
      1000000000
    );
    await provider.connection.confirmTransaction(signature);

    const user1CurrencyAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      currencyMint,
      user1.publicKey
    );
    const user1TokenAtaAddress = await getAssociatedTokenAddress(
      tokenMint,
      user1.publicKey,
      false,
      TOKEN_PROGRAM_ID,
      ASSOCIATED_TOKEN_PROGRAM_ID
    );
    await mintTo(
      provider.connection,
      payer,
      currencyMint,
      user1CurrencyAta.address,
      payer,
      BigInt(1_000_000_000)
    );

    const beforeUser1Currency = await getAccount(
      provider.connection,
      user1CurrencyAta.address
    );

    const bid1Nonce = new BN(1);
    const bid1Pda = getBidPda(
      auctionKeypair.publicKey,
      user1.publicKey,
      bid1Nonce
    );
    const tick1Pda = getTickPda(auctionKeypair.publicKey, maxPrice1);

    await program.methods
      .submitBid(bid1Nonce, bidAmount1, maxPrice1)
      .accounts({
        auction: auctionKeypair.publicKey,
        bid: bid1Pda,
        tick: tick1Pda,
        user: user1.publicKey,
        currencyMint,
        userCurrency: user1CurrencyAta.address,
        vaultAuthority: vaultAuthorityPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([user1])
      .rpc();

    const afterUser1Currency = await getAccount(
      provider.connection,
      user1CurrencyAta.address
    );
    expect(afterUser1Currency.amount).to.equal(
      beforeUser1Currency.amount - BigInt(bidAmount1.toString())
    );

    let bid1 = await program.account.bidState.fetch(bid1Pda);
    expect(bid1.amount.toString()).to.equal(bidAmount1.toString());
    expect(bid1.maxPrice.toString()).to.equal(maxPrice1.toString());

    // Place another bid from the same user (multi-bid)
    const bidAmount1b = new BN(12345);
    const maxPrice1b = new BN(600); // aligned to tickSpacing=10
    const bid1bNonce = new BN(2);
    const bid1bPda = getBidPda(
      auctionKeypair.publicKey,
      user1.publicKey,
      bid1bNonce
    );
    const tick1bPda = getTickPda(auctionKeypair.publicKey, maxPrice1b);
    await program.methods
      .submitBid(bid1bNonce, bidAmount1b, maxPrice1b)
      .accounts({
        auction: auctionKeypair.publicKey,
        bid: bid1bPda,
        tick: tick1bPda,
        user: user1.publicKey,
        currencyMint,
        userCurrency: user1CurrencyAta.address,
        vaultAuthority: vaultAuthorityPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([user1])
      .rpc();

    const bid1b = await program.account.bidState.fetch(bid1bPda);
    expect(bid1b.amount.toString()).to.equal(bidAmount1b.toString());
    expect(bid1b.maxPrice.toString()).to.equal(maxPrice1b.toString());

    // Query user's bids for this auction via helper (scheme C)
    const bids = await fetchUserBidsForAuction(
      program as any,
      auctionKeypair.publicKey,
      user1.publicKey
    );
    expect(bids.length).to.be.greaterThanOrEqual(2);

    // 2. Place Bid 2 after some time
    await new Promise((resolve) => setTimeout(resolve, 2000));
    const user2 = Keypair.generate();
    const bidAmount2 = new BN(50000);
    const maxPrice2 = new BN(500); // aligned to tickSpacing=10

    const signature2 = await provider.connection.requestAirdrop(
      user2.publicKey,
      1000000000
    );
    await provider.connection.confirmTransaction(signature2);

    const user2CurrencyAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      currencyMint,
      user2.publicKey
    );
    await mintTo(
      provider.connection,
      payer,
      currencyMint,
      user2CurrencyAta.address,
      payer,
      BigInt(1_000_000_000)
    );

    const bid2Nonce = new BN(1);
    const bid2Pda = getBidPda(
      auctionKeypair.publicKey,
      user2.publicKey,
      bid2Nonce
    );
    const tick2Pda = getTickPda(auctionKeypair.publicKey, maxPrice2);

    await program.methods
      .submitBid(bid2Nonce, bidAmount2, maxPrice2)
      .accounts({
        auction: auctionKeypair.publicKey,
        bid: bid2Pda,
        tick: tick2Pda,
        user: user2.publicKey,
        currencyMint,
        userCurrency: user2CurrencyAta.address,
        vaultAuthority: vaultAuthorityPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([user2])
      .rpc();

    let auctionAfterBid2 = await program.account.auctionState.fetch(
      auctionKeypair.publicKey
    );
    expect(auctionAfterBid2.currentFlowRate.gt(bid1.flowRate)).to.be.true;

    // 3. Claim after auction ends
    while (Math.floor(Date.now() / 1000) < endTime + 1) {
      await new Promise((resolve) => setTimeout(resolve, 1000));
    }

    await program.methods
      .claim(bid1Nonce)
      .accounts({
        auction: auctionKeypair.publicKey,
        bid: bid1Pda,
        tick: tick1Pda,
        user: user1.publicKey,
        tokenMint,
        currencyMint,
        userToken: user1TokenAtaAddress,
        userCurrency: user1CurrencyAta.address,
        vaultAuthority: vaultAuthorityPda,
        tokenVault: tokenVaultPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_PROGRAM_ID,
        associatedTokenProgram: ASSOCIATED_TOKEN_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([user1])
      .rpc();

    const bid1AfterClaim = await program.account.bidState.fetch(bid1Pda);
    const afterUser1Token = await getAccount(
      provider.connection,
      user1TokenAtaAddress
    );
    expect(afterUser1Token.amount).to.equal(
      BigInt(bid1AfterClaim.tokensFilled.toString())
    );

    // 4. Sweep raised currency + unsold tokens (auction must be graduated)
    const auctionFinal = await program.account.auctionState.fetch(
      auctionKeypair.publicKey
    );

    const beforeFundsRecipient = await getAccount(
      provider.connection,
      authorityCurrencyAta.address
    );
    await program.methods
      .sweepCurrency()
      .accounts({
        auction: auctionKeypair.publicKey,
        vaultAuthority: vaultAuthorityPda,
        currencyVault: currencyVaultPda,
        currencyMint,
        fundsRecipient: authorityCurrencyAta.address,
        tokenProgram: TOKEN_PROGRAM_ID,
      } as any)
      .rpc();
    const afterFundsRecipient = await getAccount(
      provider.connection,
      authorityCurrencyAta.address
    );
    expect(afterFundsRecipient.amount - beforeFundsRecipient.amount).to.equal(
      BigInt(auctionFinal.cumulativeDemandRaised.toString())
    );

    const beforeTokensRecipient = await getAccount(
      provider.connection,
      authorityTokenAta.address
    );
    await program.methods
      .sweepToken()
      .accounts({
        auction: auctionKeypair.publicKey,
        vaultAuthority: vaultAuthorityPda,
        tokenVault: tokenVaultPda,
        tokenMint,
        tokensRecipient: authorityTokenAta.address,
        tokenProgram: TOKEN_PROGRAM_ID,
      } as any)
      .rpc();
    const afterTokensRecipient = await getAccount(
      provider.connection,
      authorityTokenAta.address
    );
    const unsold = auctionFinal.totalSupply.sub(auctionFinal.cumulativeSupplyReleased);
    expect(afterTokensRecipient.amount - beforeTokensRecipient.amount).to.equal(
      BigInt(unsold.toString())
    );
  });

  it("Rejects low max_price griefing bid", async () => {
    const startTime = Math.floor(Date.now() / 1000) + 2;
    const endTime = startTime + 6;
    const totalSupply = new BN(1_000_000_000); // 10 tokens with 8 decimals
    const tokenDecimals = 8;
    const floorPrice = new BN(100);
    const tickSpacing = new BN(10);
    const minBidAmount = new BN(1000);
    const requiredCurrencyRaised = new BN(1);

    const tokenMint = await createMint(
      provider.connection,
      payer,
      authority,
      null,
      tokenDecimals
    );
    const currencyMint = await createMint(
      provider.connection,
      payer,
      authority,
      null,
      6
    );

    const localAuctionKeypair = Keypair.generate();
    const vaultAuthorityPda = getVaultAuthorityPda(localAuctionKeypair.publicKey);
    const tokenVaultPda = getTokenVaultPda(localAuctionKeypair.publicKey);
    const currencyVaultPda = getCurrencyVaultPda(localAuctionKeypair.publicKey);

    const authorityTokenAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      tokenMint,
      authority
    );
    const authorityCurrencyAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      currencyMint,
      authority
    );
    await mintTo(
      provider.connection,
      payer,
      tokenMint,
      authorityTokenAta.address,
      payer,
      BigInt(totalSupply.toString())
    );

    await program.methods
      .initialize(
        totalSupply,
        tokenDecimals,
        new BN(startTime),
        new BN(endTime),
        floorPrice,
        tickSpacing,
        minBidAmount,
        requiredCurrencyRaised,
        authorityTokenAta.address,
        authorityCurrencyAta.address
      )
      .accounts({
        auction: localAuctionKeypair.publicKey,
        authority: authority,
        tokenMint,
        currencyMint,
        vaultAuthority: vaultAuthorityPda,
        tokenVault: tokenVaultPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([localAuctionKeypair])
      .rpc();

    // Fund token vault so claims can succeed
    await transfer(
      provider.connection,
      payer,
      authorityTokenAta.address,
      tokenVaultPda,
      payer,
      BigInt(totalSupply.toString())
    );

    // Wait for auction to start
    while (Math.floor(Date.now() / 1000) < startTime) {
      await new Promise((resolve) => setTimeout(resolve, 1000));
    }

    const attacker = Keypair.generate();
    const signature = await provider.connection.requestAirdrop(
      attacker.publicKey,
      1000000000
    );
    await provider.connection.confirmTransaction(signature);

    const attackerCurrencyAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      currencyMint,
      attacker.publicKey
    );
    await mintTo(
      provider.connection,
      payer,
      currencyMint,
      attackerCurrencyAta.address,
      payer,
      BigInt(1_000_000_000_000)
    );

    // Attempt: huge amount but max_price only slightly above clearing price.
    // With the new on-chain lower-bound check this must be rejected.
    const bidNonce = new BN(1);
    const hugeAmount = new BN(500_000_000_000);
    const lowMaxPrice = new BN(110); // tickSpacing=10 aligned, but intentionally too low for huge amount

    const bidPda = getBidPda(localAuctionKeypair.publicKey, attacker.publicKey, bidNonce);
    const tickPda = getTickPda(localAuctionKeypair.publicKey, lowMaxPrice);

    try {
      await program.methods
        .submitBid(bidNonce, hugeAmount, lowMaxPrice)
        .accounts({
          auction: localAuctionKeypair.publicKey,
          bid: bidPda,
          tick: tickPda,
          user: attacker.publicKey,
          currencyMint,
          userCurrency: attackerCurrencyAta.address,
          vaultAuthority: vaultAuthorityPda,
          currencyVault: currencyVaultPda,
          tokenProgram: TOKEN_PROGRAM_ID,
          systemProgram: SystemProgram.programId,
        } as any)
        .signers([attacker])
        .rpc();
      throw new Error("expected submitBid to fail, but it succeeded");
    } catch (e: any) {
      const msg = e?.toString?.() ?? String(e);
      expect(msg).to.match(/MaxPriceTooLow|max price too low/i);
    }
  });

  it("Basic Auction Flow (Token-2022)", async () => {
    const startTime = Math.floor(Date.now() / 1000) + 2;
    const endTime = startTime + 6;
    const totalSupply = new BN(1000_000_000); // 10 tokens with 8 decimals
    const tokenDecimals = 8;
    const floorPrice = new BN(100);
    const tickSpacing = new BN(10);
    const minBidAmount = new BN(1000);
    const requiredCurrencyRaised = new BN(1);

    const tokenMint = await createMint(
      provider.connection,
      payer,
      authority,
      null,
      tokenDecimals,
      undefined,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    const currencyMint = await createMint(
      provider.connection,
      payer,
      authority,
      null,
      6,
      undefined,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );

    const auctionKeypair2022 = Keypair.generate();
    const vaultAuthorityPda = getVaultAuthorityPda(auctionKeypair2022.publicKey);
    const tokenVaultPda = getTokenVaultPda(auctionKeypair2022.publicKey);
    const currencyVaultPda = getCurrencyVaultPda(auctionKeypair2022.publicKey);

    const authorityTokenAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      tokenMint,
      authority,
      false,
      undefined,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    const authorityCurrencyAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      currencyMint,
      authority,
      false,
      undefined,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    await mintTo(
      provider.connection,
      payer,
      tokenMint,
      authorityTokenAta.address,
      payer,
      BigInt(totalSupply.toString()),
      [],
      undefined,
      TOKEN_2022_PROGRAM_ID
    );

    await program.methods
      .initialize(
        totalSupply,
        tokenDecimals,
        new BN(startTime),
        new BN(endTime),
        floorPrice,
        tickSpacing,
        minBidAmount,
        requiredCurrencyRaised,
        authorityTokenAta.address,
        authorityCurrencyAta.address
      )
      .accounts({
        auction: auctionKeypair2022.publicKey,
        authority: authority,
        tokenMint,
        currencyMint,
        vaultAuthority: vaultAuthorityPda,
        tokenVault: tokenVaultPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_2022_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([auctionKeypair2022])
      .rpc();

    // Fund token vault so claims can succeed
    await transfer(
      provider.connection,
      payer,
      authorityTokenAta.address,
      tokenVaultPda,
      payer,
      BigInt(totalSupply.toString()),
      [],
      undefined,
      TOKEN_2022_PROGRAM_ID
    );

    while (Math.floor(Date.now() / 1000) < startTime) {
      await new Promise((resolve) => setTimeout(resolve, 1000));
    }

    const user1 = Keypair.generate();
    const bidAmount1 = new BN(50000);
    const maxPrice1 = new BN(500);

    const signature = await provider.connection.requestAirdrop(
      user1.publicKey,
      1000000000
    );
    await provider.connection.confirmTransaction(signature);

    const user1CurrencyAta = await getOrCreateAssociatedTokenAccount(
      provider.connection,
      payer,
      currencyMint,
      user1.publicKey,
      false,
      undefined,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    const user1TokenAtaAddress = await getAssociatedTokenAddress(
      tokenMint,
      user1.publicKey,
      false,
      TOKEN_2022_PROGRAM_ID,
      ASSOCIATED_TOKEN_PROGRAM_ID
    );
    await mintTo(
      provider.connection,
      payer,
      currencyMint,
      user1CurrencyAta.address,
      payer,
      BigInt(1_000_000_000),
      [],
      undefined,
      TOKEN_2022_PROGRAM_ID
    );

    const beforeUser1Currency = await getAccount(
      provider.connection,
      user1CurrencyAta.address,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );

    const bid1Nonce = new BN(1);
    const bid1Pda = getBidPda(auctionKeypair2022.publicKey, user1.publicKey, bid1Nonce);
    const tick1Pda = getTickPda(auctionKeypair2022.publicKey, maxPrice1);

    await program.methods
      .submitBid(bid1Nonce, bidAmount1, maxPrice1)
      .accounts({
        auction: auctionKeypair2022.publicKey,
        bid: bid1Pda,
        tick: tick1Pda,
        user: user1.publicKey,
        currencyMint,
        userCurrency: user1CurrencyAta.address,
        vaultAuthority: vaultAuthorityPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_2022_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([user1])
      .rpc();

    const afterUser1Currency = await getAccount(
      provider.connection,
      user1CurrencyAta.address,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    expect(afterUser1Currency.amount).to.equal(
      beforeUser1Currency.amount - BigInt(bidAmount1.toString())
    );

    while (Math.floor(Date.now() / 1000) < endTime + 1) {
      await new Promise((resolve) => setTimeout(resolve, 1000));
    }

    await program.methods
      .claim(bid1Nonce)
      .accounts({
        auction: auctionKeypair2022.publicKey,
        bid: bid1Pda,
        tick: tick1Pda,
        user: user1.publicKey,
        tokenMint,
        currencyMint,
        userToken: user1TokenAtaAddress,
        userCurrency: user1CurrencyAta.address,
        vaultAuthority: vaultAuthorityPda,
        tokenVault: tokenVaultPda,
        currencyVault: currencyVaultPda,
        tokenProgram: TOKEN_2022_PROGRAM_ID,
        associatedTokenProgram: ASSOCIATED_TOKEN_PROGRAM_ID,
        systemProgram: SystemProgram.programId,
      } as any)
      .signers([user1])
      .rpc();

    const bid1AfterClaim = await program.account.bidState.fetch(bid1Pda);
    const afterUser1Token = await getAccount(
      provider.connection,
      user1TokenAtaAddress,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    expect(afterUser1Token.amount).to.equal(
      BigInt(bid1AfterClaim.tokensFilled.toString())
    );

    // 4. Sweep raised currency + unsold tokens (Token-2022)
    const auctionFinal = await program.account.auctionState.fetch(
      auctionKeypair2022.publicKey
    );

    const beforeFundsRecipient = await getAccount(
      provider.connection,
      authorityCurrencyAta.address,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    await program.methods
      .sweepCurrency()
      .accounts({
        auction: auctionKeypair2022.publicKey,
        vaultAuthority: vaultAuthorityPda,
        currencyVault: currencyVaultPda,
        currencyMint,
        fundsRecipient: authorityCurrencyAta.address,
        tokenProgram: TOKEN_2022_PROGRAM_ID,
      } as any)
      .rpc();
    const afterFundsRecipient = await getAccount(
      provider.connection,
      authorityCurrencyAta.address,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    expect(afterFundsRecipient.amount - beforeFundsRecipient.amount).to.equal(
      BigInt(auctionFinal.cumulativeDemandRaised.toString())
    );

    const beforeTokensRecipient = await getAccount(
      provider.connection,
      authorityTokenAta.address,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    await program.methods
      .sweepToken()
      .accounts({
        auction: auctionKeypair2022.publicKey,
        vaultAuthority: vaultAuthorityPda,
        tokenVault: tokenVaultPda,
        tokenMint,
        tokensRecipient: authorityTokenAta.address,
        tokenProgram: TOKEN_2022_PROGRAM_ID,
      } as any)
      .rpc();
    const afterTokensRecipient = await getAccount(
      provider.connection,
      authorityTokenAta.address,
      undefined,
      TOKEN_2022_PROGRAM_ID
    );
    const unsold = auctionFinal.totalSupply.sub(auctionFinal.cumulativeSupplyReleased);
    expect(afterTokensRecipient.amount - beforeTokensRecipient.amount).to.equal(
      BigInt(unsold.toString())
    );
  });

  it("Auction Failure Scenario", async () => {
    // Similar to test_auction_failure in cca.rs
    // 1. Initialize with high required raised amount
    // 2. Place small bids
    // 3. Check that it's not graduated
  });
});
