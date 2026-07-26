interface Record { id: number; tags: string[]; }
const rec: Record = { id: 7, tags: ["a", "b"] };
const text: string = JSON.stringify(rec);
const back = JSON.parse(text) as Record;
console.log(text, back.id, back.tags.length, back.tags[1]);
