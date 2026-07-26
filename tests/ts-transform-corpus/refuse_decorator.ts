function log(target: any) { return target; }
@log
class Widget { value = 1; }
console.log(new Widget().value);
