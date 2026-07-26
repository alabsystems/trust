interface Vec { x: number; y: number; }
const v: Vec = { x: 3, y: 4 };
const keys: string[] = Object.keys(v);
const vals: number[] = Object.values(v);
const entries = Object.entries(v);
const merged: Vec = { ...v, x: 10 };
console.log(keys.join(","), vals.join(","), entries.length, merged.x, merged.y);
