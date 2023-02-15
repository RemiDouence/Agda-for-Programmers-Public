# Literate Converter 

I could not use the literate markdown mode of Agda neither with
aquamacs, nor with vs code. 

So, I have developped simple file converters in Haskell.
They deal with three formats: 

1. (`.agda`) Agda with markdown as comments (each non Agda line is prefixed by
  `--MD `) This format loads fine in my Agda installation. It can be
  used to develop literate markdown files.

2. (`.lagda.md`) literate markdown 
  https://agda.readthedocs.io/en/v2.6.3/tools/literate-programming.html#literate-markdown
  I could not load this format in my Agda installation.

3. (`.agda`) Agda without markdown (the markdown as comments lines are erased)
  This format loads fine in my Agda installation. It can be used to
  focus on code.

The converters are : 

- `toLiterate` : from Agda (with markdown in comments) to literate
(from 1 to 2) 

- `toAgda` : from literate to Agda (with markdown in comments) (from 2
  to 1)

- `toPlainAgda` : from literate to Agda code only (from 2 to 3)
