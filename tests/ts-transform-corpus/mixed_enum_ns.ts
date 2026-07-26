enum Kind { Circle, Square }
namespace Factory { export function make(k: Kind): string { return k === Kind.Circle ? "round" : "boxy"; } }
console.log(Factory.make(Kind.Circle), Factory.make(Kind.Square), Kind[0]);
