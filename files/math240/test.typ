#import "./in-dexter.typ": *

// This typst file demonstrates the usage of the in-dexter package.
#set text(lang: "en", font: "Arial", size: 10pt)
#set heading(numbering: "1.1")

#set page(
  numbering: "1",
  footer: align(right)[#context {
      counter(page).display("1")
    }],
)

// Defining handy names for separate indexes to use with in-dexter in
// this document. this is easier as having to type the index parameter
// on each entry.
#let index2 = index.with(index: "Secondary")
#let index3 = index.with(index: "Tertiary")
#let indexMath = index.with(index: "Math")

// Front Matter
#align(center)[
  #text(size: 23pt)[in-dexter]
  #linebreak() #v(1em)
  #text(size: 16pt)[An index package for Typst]
  #linebreak() #v(.5em)
  #text(size: 12pt)[Version 0.7.0 (6.12.2024)]
  #linebreak() #v(.5em)
  #text(size: 10pt)[Rolf Bremer, Jutta Klebe]
  #linebreak() #v(.5em)
  #text(size: 10pt)[Contributors: \@epsilonhalbe, \@jewelpit, \@sbatial, \@lukasjuhrich, \@ThePuzzlemaker, \@hurzl]
  #v(4em)
]


// Table of Content
#outline(indent: auto, title: [Content])


= Sample Document to Demonstrate the in-dexter package

This document explains how to use the `ìn-dexter` package in typst. It contains several
samples of how to use `in-dexter` to effectively index a document. Make sure to look up
the typst code of this document to explore, what the package can do.

Using the in-dexter package in a typst document consists of some simple steps:

+ Importing the package `in-dexter`.
+ Marking the words or phrases to include in an index.
+ Generating the index page(s) by calling the `make-index()` function.


== Importing the Package

The in-dexter package is currently available on GitHub in its home repository
(https://github.com/RolfBremer/in-dexter). It is still in development and may have
breaking changes #index[Breaking Changes] in its next iteration.
#index[Iteration]#index[Development]

```typ
    #import "./in-dexter.typ": *
```

The package is also available via Typst's built-in Package Manager:

```typ
    #import "@preview/in-dexter:0.7.0": *
```

Note, that the version number of the typst package has to be adapted to get the wanted
version. It may take some time for a new version to appear in the typst universe after it
is available on GitHub.


== Marking of Entries

// This marks the start of the range for the Entry-Key "Entries"
#index(index-type: indextype.Start)[Entries]

// This marks the start of the range for the Entry-Key "Entry-Marker"
#index(index-type: indextype.Start)[Entry-Marker]

We have marked several words to be included in an index page. The markup for the entry
stays invisible#index[Invisible]. Its location in the text gets recorded, and later it is
shown as a page reference in the index page.#index([Index Page])

```typ
    #index[The Entry Phrase]
```

or

```typ
    #index([The Entry Phrase])
```

or

```typ
    #index("The Entry Phrase")
```

Entries marked this way are going to the "Default" Index. If only one index is needed,
this is the only way needed to mark entries. In-dexter can support multiple Indexes
#index[Multiple Indexes]. To specify the target index for a marking, the index must be
addressed.

```typ
    #index(index: "Secondary")[The Entry Phrase]
```

This is the explicit addressing of the secondary index.
It may be useful to define a function for the alternate index, to avoid the explicitness:


```typ
    #let index2 = index.with(index:"Secondary")

    #index2[One Entry Phrase]
    #index2[Another Entry Phrase]
```


=== Nested entries

Entries can be nested. The `index` function takes multiple arguments - one for each
nesting level.

```typ
    #index("Sample", "medical", "tissue")
    #index("Sample", "musical", "piano")
    #index("Sample")
```

#index("Sample", "medical", "tissue")
#index("Sample", "musical", "piano")
#index("Sample")


==== LaTeX Style index grouping

Alternatively or complementing to the grouping syntax above, the "bang style" syntax known
from LaTeX can be used:

// TODO: Make nice samples
```typ
    #index("Sample!medical!X-Ray")
```

#index("Sample!medical!X-Ray")

They can even be combined:

```typ
    #index("CombiGroup", "Sample!musical!Chess!")
```

#index("CombiGroup", "Sample!musical!Chess!")

Note that the last bang is not handled as a separator, but is part of the entry. To use
the bang grouping syntax, the `make-index()` function must be called with the parameter
`use-bang-grouping: true`:

```typ
    #make-index(use-bang-grouping: true)
```


=== Entries with display

These entries use an explicit display parameter. It is used to display the entry on the
index page. It can contain rich content, like math expressions:

```typ
    #index(display: "Level3", "Aaa-set3!l2!l3")
    #indexMath(display: [$cal(T)_n$-set], "Aa-set")
    #indexMath(display: [$cal(T)^n$-set], "Aa-set4")
```

#index(display: "Level3", "Aaa-set3!l2!l3")
#indexMath(display: [$cal(T)_n$-set], "Aa-set")
#indexMath(display: [$cal(T)^n$-set], "Aa-set4")

Note that display may be ignored, if entries with the same entry key are defined
beforehand. The first occurrence of an entry defines the display of all other entries with
that entry key.


=== Advanced entries

Simple math expressions can be used as entry key, like the following sample, where we also
provide an initial parameter to put sort the entry under "t" in the index:

```typ
    #indexMath(initial: "t")[$t$-tuple]
```

#indexMath(initial: "t")[$t$-tuple]

but note, that more complex ones may not be convertible to a string by in-dexter. In such
cases it is recommended to use the display parameter instead:

```typ
    #indexMath(initial: "t", display: [$cal(T)_n$-c], "Tnc")
```

#indexMath(initial: "t", display: [$cal(T)_n$-c], "Tnc")

this will put the entry in the "t" section, and uses the key ("Tnc") as sort key within
that 't' section. The entry is displayed as `$cal(T)_n$`.

The following entry will place the entry in the "D" section, because we have not provided
an explicit `initial` parameter, so the section is derived from the keys first letter
("DTN").

```typ
    #indexMath(display: [d-$cal(T)_n$], "DTN")
```

#index(display: [d-$cal(T)_n$], "DTN")


The index-function to mark entries also accepts a tuple value:

```typ
    #indexMath(([d-$rho_x$], "RTX"))
```

#indexMath(([d-$rho_x$], "RTX"))

The first value of the tuple is interpreted as the `display`, the second as the `key`
parameter.


// More samples and tests
#indexMath(([d-$phi_x^2*sum(d)$], "DPX"))

#index(index-type: indextype.End)[Entry-Marker]


==== Suppressing the casing for formulas

Sometimes, the entry-casing of the `make-index()` function should not apply to an entry.
This is often the case for math formulas. The `index()` function therefore has a parameter
`apply-casing`, that allows to suppress the application of the entry-casing function for
this specific entry.

```typ
#index(display: $(n, k)"-representable"$, "nkrepresentable", apply-casing: false)
```

#index(display: $(n, k)"-representable"$, "nkrepresentable", apply-casing: false)


Note: If multiple entries have the same key, but different apply-casing flags, the first
one wins.

```typ
#index(display: $(x, p)"-double"$, "xprepresentable", apply-casing: false)
#index(display: $(x, p)"-double"$, "xprepresentable", apply-casing: true)
```

#index(display: $(x, p)"-double"$, "xprepresentable", apply-casing: false)
#index(display: $(x, p)"-double"$, "xprepresentable", apply-casing: true)


==== Symbols

Symbols can be indexed to be sorted under `"Symbols"`, and be sorted at the top of the
index like this

```typ
    #indexMath(initial: (letter: "Symbols", sort-by: "#"), [$(sigma)$])
```

#indexMath(initial: (letter: "Symbols", sort-by: "#"), [$(sigma)$])


==== Formatting Entries

#index(fmt: strong, [Formatting Entries])

Entries can be formatted with arbitrary functions that map `content` to `content`

```typ
    #index(fmt: it => strong(it), [The Entry Phrase])
```

or shorter

```typ
    #index(fmt: strong, [The Entry Phrase])
```

For convenience in-dexter exposes `index-main` which formats the entry bold. It is
semantically named to decouple the markup from the actual style. One can decide to have
the main entries slanted or color formatted, which makes it clear that the style should
not be part of the function name in markup. Naming markup functions according to their
purpose (semantically) also eases the burden on the author, because she must not remember
the currently valid styles for her intent.

Another reason to use semantically markup functions is to have them defined in a central
place. Changing the style becomes very easy this way.

```typ
    #index-main[The Entry Phrase]
```

It is predefined in in-dexter like this:

```typ
    #let index-main = index.with(fmt: strong)
```

Here we define another semantical index marker, which adds an "ff." to the page number.

```typ
    #let index-ff = index.with(fmt: it => [#it _ff._])
```

#let index-ff = index.with(fmt: it => [#it _ff._])


==== Referencing Ranges and Continuations

Up to this point, we used Cardinal Markers#index[Cardinal Markers] to mark the index
entries. They are referred to with their single page number from the index page. But
`in-dexter` also supports more advanced references to marked entries, like the following:

- Ranges of Pages:
  - 42-46
  - 42-46, 52-59

- Single Page Continuation (SPC):
  - 77f.
  - 77+

- Multi-Page Continuation (MPC):
  - 82ff.
  - 77-
  - 77++

The Continuation Symbols ("f.", "ff.") symbols can be customized via parameters `spc` and
`mpc` to `make-index()`.

This Sample uses "+" for _Single Page Continuation_ and "++" for _Multi Page Continuations_.
```typ
  #make-index(
    use-bang-grouping: true,
    use-page-counter: true,
    sort-order: upper,
    spc: "+",
    mpc: "++",
  )
```


If `spc` is set to `none`, an explicit numeric range is used, like "42-43".
If `mpc` is set to `none`, an explicit numeric range is used, like "42-49".

Note that "f." and "ff." are the default symbols for `scp` and `mcp`.


===== Range of Pages

To mark a Range of pages for an index entry, one can use the following marker:

```typ
#index(index-type: indextype.Start)[Entry]

// other content here

#index(index-type: indextype.End)[Entry]
```

Of course, you can shorten this somewhat explicit marker with your own marker, like this:

#let index-start = index.with(index-type: indextype.Start)
#let index-end = index.with(index-type: indextype.End)


Behavior:

- If the markers are on the same resulting page, they are automatically combined to a
  Cardinal Marker#index[Cardinal Marker] in the generated index page.

- If the End-Marker is on the next page following the Start-Marker, the Marker is handled
  as a Continuation Marker ("f."). If it uses the Continuation Symbol or the page numbers
  can be configured in a Parameter of `make-index()`.

- If there is a Start-Marker, but no End-Marker, the Marker is handled as a Continuation
  Marker ("ff.").


== The Index Page

#index[Index Page]

To actually create the index page, the `make-index()` function has to be called. Of course,
it can be embedded into an appropriately formatted #index[Formatting]
environment#index[Environment], like this:

```typ
    #columns(3)[
        #make-index()
    ]
```

The `make-index()` function accepts an optional array of indexes to include into the index
page. The default value, `auto`, takes all entries from all indexes. The following sample
only uses the entries of the secondary and tertiary index. See sample output in
@combinedIndex.

```typ
    #columns(3)[
        #make-index(indexes: ("Secondary", "Tertiary"))
    ]
```


=== Skipping physical pages

If page number 1 is not the first physical page#index-main[physical page] of the document,
the parameter ` use-page-counter` of the `make-index()` function can be set to `true`.
Default is `false`. In-dexter uses the page counter instead of the physical page number
then.


= Why Having an Index in Times of Search Functionality?
#index(fmt: strong, [Searching vs. Index])

A _hand-picked_#index[Hand Picked] or _handcrafted_#index[Handcrafted] Index in times of
search functionality seems a bit old-fashioned#index[Old-fashioned] at the first glance.
But such an index allows the author to direct the reader, who is looking for a specific
topic#index-main("Topic", "specific") (using index-main), to exactly the right places.

Especially in larger documents#index[Large Documents] and books#index[Books] this becomes
very useful, since search engines#index[Search Engines]#index3[Engines] may
provide#index[Provide] too many locations of specific#index2[specific] words. The
index#index[Index] is much more comprehensive,#index[Comprehensive] assuming that the
author#index[Authors responsibility] has its content#index[Content] selected well. Authors
know best where a certain topic#index("Topic", "certain") is explained#index[Explained]
thoroughly#index[Thoroughly] or merely noteworthy #index[Noteworthy] mentioned (using the
`index` function).

Note, that this document is not necessarily a good example#index2[example] of the index.
Here we just need to have as many index entries#index[Entries] as possible to
demonstrate#index-ff([Demonstrate]) (using a custom made `index-ff` function) the
functionality #index[Functionality] and have a properly#index[Properly]
filled#index3[filled] index at the end.

Even for symbols like `(ρ)`.
#index([$(rho)$], initial: (letter: "Symbols", sort-by: "#"), apply-casing: false)
Indexing should work for for any Unicode string like Cyrillic
(Скороспелка#index(initial: (letter: "С", sort-by: "Ss"), "Скороспелка")) or German
(Ölrückstoßabdämpfung).#index(initial: (letter: "Ö", sort-by: "Oo"),
"Ölrückstoßabdämpfung") - though we need to add initials:

`#index(initial: (letter: "С", sort-by: "Ss"), "Скороспелка")`

or

`#index(initial: (letter: "Ö", sort-by: "Oo"), "Ölrückstoßabdämpfung")`.


#line(length: 100%, stroke: .1pt + gray)

#pagebreak()

#set page(
  numbering: "i",
  footer: align(right)[#context {
      counter(page).display("i")
    }],
)

// This marks the end of the range for the Entry-Key "Entries"
#index(index-type: indextype.End)[Entries]


= Index pages

In this chapter we emit several index pages for this document. We also switched page
numbering to roman numbers#index[Roman Numbers], to demonstrate in-dexters ability to
display them, if the option `use-page-counter` has been set to true.

// Table of Content from here on
#context (outline(title: none, target: selector(heading).after(here())))


== The Default Index page<defaultIndex>

Here we generate the Index page in three columns. The default behavior (auto) is to use
all indexes together.

#index-main[Metadaten!Primäre]
#index-main(display: "Joy")[Metadaten!Sekundäre!Fun]
#index-main("Metadaten!Tertiäre")

// A sample with a raw display text
#index(display: `Aberration`, "Aberration")


#columns(3)[
  #make-index(
    use-bang-grouping: true,
    use-page-counter: true,
    sort-order: upper,
    range-delimiter: [--]
  )
]

#pagebreak()


== Secondary Index

Here we select explicitly only the secondary index.

#columns(3)[
  #make-index(indexes: "Secondary", use-bang-grouping: true, sort-order: upper)
]

#line(length: 100%)


== Tertiary Index

Here we select explicitly only the tertiary index.

#columns(3)[
  #make-index(
    indexes: "Tertiary",
    use-bang-grouping: true,
    sort-order: upper,
  )
]

#line(length: 100%)


== Combined Index<combinedIndex>

Here we select explicitly secondary and tertiary indexes.

#columns(3)[
  #make-index(
    indexes: ("Secondary", "Tertiary"),
    use-bang-grouping: true,
    sort-order: upper,
  )
]

#line(length: 100%)


== Combined Index - all lower case

Here we select explicitly secondary#index[Secondary Index] and tertiary#index[Tertiary
Index] indexes and format them all lower case.

#columns(3)[
  #make-index(
    indexes: ("Secondary", "Tertiary"),
    entry-casing: lower,
    use-bang-grouping: true,
    sort-order: upper,
  )
]

#line(length: 100%)
#pagebreak()


== Math Index

Here we explicitly select only the Math index.

#columns(3)[
  #make-index(
    indexes: ("Math"),
    sort-order: upper,
    use-bang-grouping: true,
  )
]