type Entry = [string, number];
const pairs: Entry[] = [["a", 1], ["b", 2], ["c", 3]];
let keys: string = "";
let vsum: number = 0;
for (const [k, v] of pairs) { keys += k; vsum += v; }
const swapped: [number, string] = [pairs[0][1], pairs[0][0]];
console.log(keys, vsum, swapped[0], swapped[1]);
