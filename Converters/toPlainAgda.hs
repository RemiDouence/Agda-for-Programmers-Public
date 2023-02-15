
main = interact (unlines . stripMarkdown . lines)

stripMarkdown :: [String] -> [String]
stripMarkdown [] = []
stripMarkdown (l:ls)
  | isCommentBlock l = "" : keepBlock ls
  | otherwise        = stripMarkdown ls

keepBlock :: [String] -> [String]
keepBlock [] = []
keepBlock (l:ls)
  | isCommentBlock l = stripMarkdown ls
  | otherwise = l : keepBlock ls

isCommentBlock :: String -> Bool
isCommentBlock cs = take (length (comment block)) cs == comment block

block :: String
block = "```"

prefix :: String
prefix = "--MD " 

comment :: String -> String
comment cs = prefix ++ cs
