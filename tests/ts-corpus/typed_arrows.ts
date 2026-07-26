const dbl = (x: number): number => x * 2;
const cat = (a: string, b: string): string => a + b;
const apply = (f: (n: number) => number, v: number): number => f(v);
const nums: number[] = [1, 2, 3].map((n: number): number => n + 1);
console.log(dbl(5), cat("a", "b"), apply(dbl, 10), nums.join(","));
