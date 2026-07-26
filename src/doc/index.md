% Trust Documentation

<style>
nav {
    display: none;
}
h3 {
    font-size: 1.35rem;
}
h4 {
    font-size: 1.1rem;
}

/* Formatting for docs search bar */
#search-input {
    width: calc(100% - 58px);
}
#search-but {
    cursor: pointer;
}
#search-but, #search-input {
    padding: 4px;
    border: 1px solid #ccc;
    border-radius: 3px;
    outline: none;
    font-size: 0.7em;
    background-color: #fff;
}
#search-but:hover, #search-input:focus {
    border-color: #55a9ff;
}

/* Formatting for external link icon */
svg.external-link {
  display: inline-block;
  position: relative;
  vertical-align: super;
  width: 0.7rem;
  height: 0.7rem;
  padding-left: 2px;
  top: 3px;
}
</style>

This is the documentation shipped with the [Trust toolchain]: one book per tool
in the sysroot, plus the API reference for the standard library. It is available
offline — everything linked below is part of this installation.

Trust accepts two authoritative languages for program objects, specifications
and proofs: Rust and Lean-compatible Clean. Documentation of the *languages*
themselves is not part of this set; the pages here document the tools Trust
builds and ships.

If you're just looking for the standard library reference, here it is:
[API documentation](std/index.html)


## The toolchain

### The `trustc` Book

[The `trustc` Book](rustc/index.html) documents the compiler: command-line
arguments, lints, JSON output, target support, code coverage, exploit
mitigations and symbol mangling.

### The Unstable Book

[The Unstable Book](unstable-book/index.html) documents the unstable surface —
every `-Z` compiler flag and unstable language feature, including Trust's own
verification flags.

### Extended Error Listing

Diagnostics carry error codes, and you can request an extended explanation from
the compiler with `trustc --explain`. The same explanations are collected here:
[error index](error-index.html)

### The Cargo Book

[The Cargo Book](cargo/index.html) documents `targo`, the build tool and
dependency manager, whose command surface and manifest format Trust keeps
compatible with Cargo's.

### The Trustdoc Book

[The Trustdoc Book](rustdoc/index.html) documents `trustdoc`, the documentation
generator that produced these pages.

### The Tippy Book

[The Tippy Book](tippy/index.html) documents Trust's static analyzer. Its lint
namespace remains `clippy::` for source compatibility with existing projects.


## The standard library

The standard library has [extensive API documentation](std/index.html), with
explanations of how to use various things, as well as example code for
accomplishing various tasks.

<div>
  <form action="std/index.html" method="get">
    <input id="search-input" type="search" name="search"
           placeholder="Search through the standard library"/>
    <button id="search-but">Search</button>
  </form>
</div>


## Your own crates

Inside any crate, `targo doc --open` generates documentation for the crate and
all of its dependencies at their resolved versions, and opens it in your
browser. Add `--document-private-items` to include items not marked `pub`.

[Trust toolchain]: https://github.com/alabsystems/trust

<script>
// check if a given link is external
function isExternalLink(url) {
  const tmp = document.createElement('a');
  tmp.href = url;
  return tmp.host !== window.location.host;
}

// Add the `external` class to all <a> tags with external links and append the external link SVG
function updateExternalAnchors() {
  /*
    External link SVG from Font-Awesome
    CC BY-SA 3.0 https://creativecommons.org/licenses/by-sa/3.0
    via Wikimedia Commons
  */
  const svgText = `<svg
     class='external-link'
     xmlns='http://www.w3.org/2000/svg'
     viewBox='0 -256 1850 1850'
     width='100%'
     height='100%'>
       <g transform='matrix(1,0,0,-1,30,1427)'>
         <path d='M 1408,608 V 288 Q 1408,169 1323.5,84.5 1239,0 1120,
           0 H 288 Q 169,0 84.5,84.5 0,169 0,288 v 832 Q 0,1239 84.5,1323.5 169,
           1408 288,1408 h 704 q 14,0 23,-9 9,-9 9,-23 v -64 q 0,-14 -9,-23 -9,
           -9 -23,-9 H 288 q -66,0 -113,-47 -47,-47 -47,-113 V 288 q 0,-66 47,
           -113 47,-47 113,-47 h 832 q 66,0 113,47 47,47 47,113 v 320 q 0,14 9,
           23 9,9 23,9 h 64 q 14,0 23,-9 9,-9 9,-23 z m 384,864 V 960 q 0,
           -26 -19,-45 -19,-19 -45,-19 -26,0 -45,19 L 1507,1091 855,439 q -10,
           -10 -23,-10 -13,0 -23,10 L 695,553 q -10,10 -10,23 0,13 10,23 l 652,
           652 -176,176 q -19,19 -19,45 0,26 19,45 19,19 45,19 h 512 q 26,0 45,
           -19 19,-19 19,-45 z' style='fill:currentColor' />
         </g>
     </svg>`;
  let allAnchors = document.getElementsByTagName("a");

  for (var i = 0; i < allAnchors.length; ++i) {
    let anchor = allAnchors[i];
    if (isExternalLink(anchor.href)) {
      anchor.classList.add("external");
      anchor.innerHTML += svgText;
    }
  }
}

// on page load, update external anchors
document.addEventListener("DOMContentLoaded", updateExternalAnchors);

</script>
