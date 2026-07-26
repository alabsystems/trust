function makeCounter(start: number): () => number {
  let n: number = start;
  return (): number => { n += 1; return n; };
}
const c: () => number = makeCounter(10);
const adder = (base: number) => (x: number): number => base + x;
const add5 = adder(5);
console.log(c(), c(), c(), add5(100), add5(1));
