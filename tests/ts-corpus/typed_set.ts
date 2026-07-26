const seen: Set<number> = new Set<number>([1, 2, 2, 3, 3, 3]);
seen.add(4);
seen.delete(1);
let count: number = 0;
seen.forEach((): void => { count += 1; });
console.log(seen.size, seen.has(2), seen.has(1), count);
