// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><a href="index.html"><strong aria-hidden="true">1.</strong> grmtools</a></li><li class="chapter-item expanded "><a href="quickstart.html"><strong aria-hidden="true">2.</strong> Quickstart Guide</a></li><li class="chapter-item expanded "><a href="lexing.html"><strong aria-hidden="true">3.</strong> Lexing</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="lexcompatibility.html"><strong aria-hidden="true">3.1.</strong> Lex compatibility</a></li><li class="chapter-item expanded "><a href="manuallexer.html"><strong aria-hidden="true">3.2.</strong> Hand-written lexers</a></li><li class="chapter-item expanded "><a href="start_states.html"><strong aria-hidden="true">3.3.</strong> Start States</a></li></ol></li><li class="chapter-item expanded "><a href="parsing.html"><strong aria-hidden="true">4.</strong> Parsing</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="yacccompatibility.html"><strong aria-hidden="true">4.1.</strong> Yacc compatibility</a></li><li class="chapter-item expanded "><a href="actioncode.html"><strong aria-hidden="true">4.2.</strong> Return types and action code</a></li><li class="chapter-item expanded "><a href="parsing_idioms.html"><strong aria-hidden="true">4.3.</strong> grmtools parsing idioms</a></li><li class="chapter-item expanded "><a href="errorrecovery.html"><strong aria-hidden="true">4.4.</strong> Error recovery</a></li><li class="chapter-item expanded "><a href="ast_example.html"><strong aria-hidden="true">4.5.</strong> An AST evaluator</a></li></ol></li><li class="chapter-item expanded "><a href="editions.html"><strong aria-hidden="true">5.</strong> Rust Editions</a></li><li class="chapter-item expanded "><a href="libsandtools.html"><strong aria-hidden="true">6.</strong> The individual libraries and tools</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="lrpar.html"><strong aria-hidden="true">6.1.</strong> lrpar</a></li><li class="chapter-item expanded "><a href="lrlex.html"><strong aria-hidden="true">6.2.</strong> lrlex</a></li><li class="chapter-item expanded "><a href="nimbleparse.html"><strong aria-hidden="true">6.3.</strong> nimbleparse</a></li><li class="chapter-item expanded "><a href="cfgrammar.html"><strong aria-hidden="true">6.4.</strong> cfgrammar</a></li><li class="chapter-item expanded "><a href="lrtable.html"><strong aria-hidden="true">6.5.</strong> lrtable</a></li><li class="chapter-item expanded "><a href="thirdparty.html"><strong aria-hidden="true">6.6.</strong> third party</a></li></ol></li><li class="chapter-item expanded "><a href="othertools.html"><strong aria-hidden="true">7.</strong> Other Rust parsing tools</a></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0].split("?")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
