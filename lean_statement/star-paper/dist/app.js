"use strict";
// Native <details> keeps each formalization in the reading flow, including
// without JavaScript. Opening one never changes focus, the URL, or scroll.
const toggle = document.getElementById("annotations-toggle");
toggle.addEventListener("change", () => {
  document.body.classList.toggle("reading-only", !toggle.checked);
});
