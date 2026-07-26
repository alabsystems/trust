const enum Level { Low, Medium = 5, High }
console.log(Level.Low, Level.Medium, Level.High);
console.log(Level[0], Level[5], Level[6], JSON.stringify(Level));
