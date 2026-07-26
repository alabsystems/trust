function sealed(target: unknown) { return target; }
@sealed
class Widget { value = 1; }
console.log(new Widget().value);
