namespace Bank { let rate = 0.05; export const name = "Acme"; export function interest(amount: number): number { return amount * rate; } }
console.log(Bank.name, Bank.interest(1000), JSON.stringify(Bank));
