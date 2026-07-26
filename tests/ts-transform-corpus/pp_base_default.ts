class Counter { constructor(public count: number = 10, private step: number = 2) {} next(): number { return this.count + this.step; } }
const a = new Counter();
const b = new Counter(100);
console.log(a.next(), b.next(), a.count, b.count);
