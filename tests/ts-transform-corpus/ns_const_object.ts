namespace Log { export const entries: number[] = []; export function add(n: number): void { entries.push(n); } }
Log.add(1); Log.add(2); Log.add(3);
console.log(Log.entries, Log.entries.length, JSON.stringify(Log));
