const xs: number[] = [5, 3, 9, 1, 7];
const doubled: number[] = xs.map((n: number): number => n * 2);
const evens: number[] = xs.filter((n: number): boolean => n % 2 === 1);
const total: number = xs.reduce((a: number, b: number): number => a + b, 0);
const found: number | undefined = xs.find((n: number): boolean => n > 6);
console.log(doubled.join(","), evens.join(","), total, found, xs.includes(9));
