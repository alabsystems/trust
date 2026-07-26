function fact(n: number): number { return n <= 1 ? 1 : n * fact(n - 1); }
function fib(n: number): number { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
console.log(fact(5), fact(6), fib(10), fib(15));
