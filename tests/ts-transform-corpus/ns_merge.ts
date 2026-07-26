namespace Store { export const items = 3; export function itemCount(): number { return items; } }
namespace Store { export const price = 9; export function priceTag(): string { return "$" + price; } }
console.log(Store.items, Store.price, Store.itemCount(), Store.priceTag(), JSON.stringify(Store));
