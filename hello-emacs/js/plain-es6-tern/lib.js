/**
 * The version of this library.
 */
export const kVersion = "0.1.0";

/**
 * Add x and y together.
 */
export function add(x, y) {
  return x + y;
}

// A list.
export class List {
  constructor() {
    this.xs = [];
  }

  // Push one element.
  push(x) {
    this.xs.push(x);
  }

  // Returns the length of the list.
  len() {
    return this.xs.length;
  }
}

//module.exports = { kVersion, add, List };
