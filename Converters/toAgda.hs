
main = interact (unlines . convertMarkdown . lines)

convertMarkdown :: [String] -> [String]
convertMarkdown [] = []
convertMarkdown (l:ls)
  | isBlock l = comment l : convertBlock ls
  | otherwise = comment l : convertMarkdown ls

convertBlock :: [String] -> [String]
convertBlock (l:ls)
  | isBlock l = comment l : convertMarkdown ls
  | otherwise = l : convertBlock ls

block :: String
block = "```"

isBlock :: String -> Bool
isBlock cs = take (length block) cs == block

prefix :: String
prefix = "--MD " 

comment :: String -> String
comment cs = prefix ++ cs
