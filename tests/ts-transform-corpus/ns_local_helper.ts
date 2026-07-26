namespace Str { function reverse(s: string): string { return s.split("").reverse().join(""); } export function palindrome(s: string): boolean { return s === reverse(s); } }
console.log(Str.palindrome("racecar"), Str.palindrome("hello"));
