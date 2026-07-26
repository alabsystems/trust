const s: string = "Trust Verification";
const upper: string = s.toUpperCase();
const parts: string[] = s.split(" ");
const joined: string = parts.join("-");
const sliced: string = s.slice(0, 5);
const idx: number = s.indexOf("V");
console.log(upper, joined, sliced, idx, s.length, s.replace("Trust", "T"));
