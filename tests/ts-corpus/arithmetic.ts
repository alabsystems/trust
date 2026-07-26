function poly(x: number): number { return 3 * x * x - 2 * x + 7; }
const ints: number[] = [0, 1, 2, 3, 4];
let acc: number = 0;
for (const n of ints) { acc += poly(n); }
const q: number = 17 % 5;
const p: number = 2 ** 10;
console.log(acc, q, p, Math.abs(-9), Math.max(3, 8, 1), Math.floor(7.9));
