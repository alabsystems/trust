namespace Calc { function double(n: number): number { return n * 2; } const base = 5; export function scaled(n: number): number { return double(n) + base; } export const origin = base; }
console.log(Calc.scaled(3), Calc.origin, JSON.stringify(Calc));
