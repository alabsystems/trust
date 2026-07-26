enum Suit { Hearts, Diamonds, Clubs, Spades }
enum Rank { Two = 2, Three, Four }
console.log(Suit.Spades, Rank.Four, Suit[3], Rank[4]);
console.log(JSON.stringify(Suit), JSON.stringify(Rank));
