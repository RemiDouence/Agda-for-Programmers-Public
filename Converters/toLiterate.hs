
main = interact (unlines . restoreMarkdown . lines)

restoreMarkdown :: [String] -> [String]
restoreMarkdown = map unComment

unComment :: String -> String
unComment cs | isComment cs = drop (length prefix) cs
             | otherwise    = cs

isComment :: String -> Bool
isComment cs = take 5 cs == prefix

prefix :: String
prefix = "--MD " 
