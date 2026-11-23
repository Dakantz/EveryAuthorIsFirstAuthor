import { findClusterBreak } from "@marijn/find-cluster-break"
import { getElementFont, getElementFontString, getTextWidth } from "./text_width";
import { prepare, prepareWithSegments } from "@chenglou/pretext";

class EqualizedAuthor {
    constructor(public name: string, public natural_w: number, public w: number, public s: number, public t: number) { }
}
class AuthorStats {
    constructor(public name: string, public w: number, public c: number, public g: number, public K: number) { }
}
export const graphemeCount = (s: string): number => {
    let cnt = 0;
    let pos = 0;
    while (pos < s.length) {
        const nextPos = findClusterBreak(s, pos);
        cnt++;
        pos = nextPos;
    }
    return cnt;
}
export function sum(arr: number[]): number {
    return arr.reduce((acc, val) => acc + val, 0);
}
export const stat = (author: string, css: string, alpha: number = 1, beta: number = 1): AuthorStats => {
    const w = getTextWidth(author, css);
    console.log(`Author: ${author}, width: ${w}, font: ${css}`);
    const c = graphemeCount(author);

    let g = c - 1;
    let e = w / c
    let K = w * w / alpha + g * g * e * e / beta
    return new AuthorStats(author, w, c, g, K);
};
const solveAuthor = (stat: AuthorStats, W: number, alpha: number, beta: number, smin: number = 0.85, smax: number = 1.15): EqualizedAuthor => {
    let lam = (W - stat.w) / stat.K;
    console.log(`Solving author: ${stat.name}, W: ${W}, w: ${stat.w}, K: ${stat.K}, lam: ${lam}`);
    let s = 1 + lam * stat.w / alpha;
    // s = Math.max(smin, Math.min(smax, s));
    let t = 0;
    if (stat.g === 0) {
        t = 0;
    } else {
        t = (W - stat.w * s) / stat.g;
    }
    return new EqualizedAuthor(stat.name, stat.w, stat.w + lam * stat.K, s, t);
};
const styleContainer = (element: HTMLElement): void => {
    element.style.padding = "0";
    element.style.margin = "0";
    element.style.display = "flex";
    element.style.flexDirection = "column";
    element.style.alignItems = "start";
    element.style.justifyContent = "start";
};
const styleAuthor = (div: HTMLElement, author: EqualizedAuthor, font: string): void => {
    div.style.margin = "0";
    div.style.padding = "0";
    div.style.letterSpacing = `${author.t}px`;
    div.style.transform = `scaleX(${author.s})`;
    div.style.transformOrigin = "left"; // default is center, which leaves a gap on the left
    div.style.float = "left";
};
export const solve = (authors: string[], fontString: string, alpha: number, beta: number): EqualizedAuthor[] => {
    const stats = authors.map(a => stat(a, fontString, alpha, beta));
    const optimal_width = stats.reduce((acc, s) => acc + s.w / s.K, 0) / stats.reduce((acc, s) => acc + 1 / s.K, 0);
    return stats.map(s => solveAuthor(s, optimal_width, alpha, beta));
};
const appendAuthor = (element: HTMLElement, author: EqualizedAuthor, font: string): HTMLDivElement => {
    const div = document.createElement("div");
    styleAuthor(div, author, font);
    div.innerText = author.name;
    element.appendChild(div);
    return div;
};
export const equalizeAuthorsOnto = (authors: string[], element: HTMLElement, alpha: number = 1, beta: number = 1): void => {
    styleContainer(element);
    const fontString = getElementFontString(element);
    const solved_authors = solve(authors, fontString, alpha, beta);
    // stack authors on top of each other via absolute positioning
    for (const author of solved_authors) {
        appendAuthor(element, author, fontString).style.position = "absolute";
    }
    element.style.minHeight = `1rem`;
}
export const equalizeAuthorsStack = (authors: string[], element: HTMLElement, alpha: number = 1, beta: number = 1) => {
    styleContainer(element);
    element.style.clear = "both";
    const fontString = getElementFontString(element);
    const solved_authors = solve(authors, fontString, alpha, beta);
    for (const author of solved_authors) {
        appendAuthor(element, author, fontString).style.display = "block";
    }
    return solved_authors;
}
