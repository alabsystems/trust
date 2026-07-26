enum Priority { Low = 1, High = 2 }
const table: Record<string, Priority> = { a: Priority.Low, b: Priority.High };
function pick(name: string): Priority { return table[name]; }
console.log(pick("a"), pick("b"), Priority[pick("b")]);
