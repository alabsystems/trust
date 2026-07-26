type Foo = number;
type Bar = string;
const value = 42;
const other = "kept";
export { type Foo, value, type Bar, other };
console.log(value, other);
