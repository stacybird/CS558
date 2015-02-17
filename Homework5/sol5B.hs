-- Homework 5  Stacy Watts   swatts@pdx.edu

-- rev:: [a] -> [a] reverses an arbitrary list. You make take the "built-in"
-- library function (++) (append) as primitive. The function you write should
-- reverse a list. For example rev [1,2,5] ---> [5,2,1]. 

rev a = foldr (\x list -> list ++ [x] ) [] a

-- forall : (a -> Bool) -> [a] -> Bool , where (forall f l) returns True, if
-- for every element x in l , (f x) evaluates to True , or l is empty. 

-- baby idea...  I think i nee
-- forall a = (\x (list -> Bool) -> [list] -> Bool ) [] a


