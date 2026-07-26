const scores: Map<string, number> = new Map<string, number>();
scores.set("a", 1);
scores.set("b", 2);
scores.set("a", 10);
let sum: number = 0;
for (const v of scores.values()) { sum += v; }
console.log(scores.size, scores.get("a"), scores.has("c"), sum);
