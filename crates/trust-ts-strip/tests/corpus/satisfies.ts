const config = { host: "localhost", port: 8080 } satisfies Record<string, string | number>;
const nums = [1, 2, 3] satisfies number[];
console.log(config.host, config.port, nums.length);
