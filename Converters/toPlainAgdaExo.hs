
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
  | isExo l = mkExo l : skipSolution ls
  | otherwise = l : keepBlock ls

skipSolution :: [String] -> [String]
skipSolution (l:ls) 
  | isEmpty l = l : keepBlock ls
  | isCommentBlock l = stripMarkdown ls
  | otherwise = skipSolution ls

isCommentBlock :: String -> Bool
isCommentBlock cs = take (length (comment block)) cs == comment block

block :: String
block = "```"

prefix :: String
prefix = "--MD " 

comment :: String -> String
comment cs = prefix ++ cs

exo :: String
exo = "--EXO "

isExo :: String -> Bool
isExo cs = take (length exo) cs == exo

mkExo :: String -> String
mkExo = drop (length exo) 

isEmpty :: String -> Bool
isEmpty = all (' '==)
