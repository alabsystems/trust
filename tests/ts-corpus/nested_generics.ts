const grid: Array<Array<number>> = [[1, 2], [3, 4]];
const lookup: Map<string, Array<number>> = new Map<string, Array<number>>();
lookup.set("a", [1, 2, 3]);
const deep: Map<string, Map<string, number>> = new Map();
console.log(grid[1][0], lookup.get("a")!.length, deep.size);
