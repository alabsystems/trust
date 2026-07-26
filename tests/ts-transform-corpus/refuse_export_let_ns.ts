namespace Counter { export let count = 0; export function inc(): void { count++; } }
Counter.inc();
console.log(Counter.count);
