{-# OPTIONS -XScopedTypeVariables #-}

import Data.SBV
import Data.Map (toList)
import Data.List ((\\),sort,foldl')
import Safe (headMay,readMay)
import Data.List.Split (splitOn)
import Debug.Trace
import Text.Parsec
import System.IO.Strict (readFile)
import System.Environment (getArgs)
import System.Console.ANSI

-- INPUT BEGIN
spec = Spec {
-- 0-origin, sorted, and no gap
  nights = 2 ,
  least_capacity_diff = 2 ,
  nonstays = [(1,0),(3,1),(5,1),(7,1),(8,1),(9,1)] ,
  rooms_capacity = [(201,[3,3]),
                    (202,[3,3]),
                    (203,[5,4]),
                    (204,[3,0]),
                    (205,[2,2])
                   ] ,
-- 0 and 2 share a room
-- 1, 3, and 8 share a room
  shared = [[0,2],[1,3,8]]
  }

-- 1 does not stay at the 0th day
-- [3,5,7,8,9] does not stay at the 1st day
-- unshared :: [([Int],[Int])]
unshared mems =
  [([4,5,6],[7,9]),                           -- don't like
   ([0,2,12,13],(mems)\\[0,2,12,13]), -- male/female
   ([1,3,8],(mems)\\[1,3,8]),         -- earlysleeper
   ([0,2],(mems)\\[0,2])              -- smoker/nonsmoker
  ]

additional :: SArray Integer Integer -> Symbolic ()
additional =
      \mm -> do -- 12 uses 202
                constrain
                 (array mm (12,0) .== 202)
-- INPUT END

-- @tadokoro's CSV parser https://qiita.com/tadokoro/
csvStruct = endBy line eol
line = sepBy cell $ char ','
cell = many $ noneOf ",\n"
eol = char '\n'
parseCSV :: String -> Either ParseError [[String]]
parseCSV = parse csvStruct "* ParseError *"

data Spec = Spec {
  nights :: Int ,
  least_capacity_diff :: Int ,
  nonstays :: [(Int,Int)] ,
  rooms_capacity :: [(Int,[Int])] ,
  shared :: [[Int]]
  }

total mems = concatMap (\x -> map (\j -> (x,j)) [0..((nights spec)-1)]) mems
flat (i,j) = fromIntegral ((nights spec)*i+j)
unflat i = (i `div` (nights spec),i `mod` (nights spec))
nonstayroom = 999

initialize mems =
 do mem_vars <- (sIntegers . map (show . flat) . total) (mems)
    m0 :: SArray Integer Integer <- newArray_ Nothing
    return (foldr
             (\(y,z) x -> writeArray x (flat y) z)
             m0
             (zip (total (mems)) mem_vars)
           )

array mm = readArray mm . flat

problem :: [Int] -> Predicate
problem mems =
 do mm <- initialize mems
    mapM_
     (\i ->
       mapM_
        (\(x,y) ->
          constrain
           (array mm (i,x) .== array mm (i,y) |||
            array mm (i,x) .== nonstayroom |||
            array mm (i,y) .== nonstayroom
           )
        )
        (prod [0..((nights spec)-1)] [0..((nights spec)-1)])
     )
     (mems)
    mapM_
       (\i ->
          constrain
          (if i `elem` nonstays spec
           then array mm i .== nonstayroom
           else array mm i `sElem` (map (fromIntegral . fst) (rooms_capacity spec))
          )
       )
       (total (mems))
    mapM_
       (\z ->
          (mapM_
           (\(x,y) ->
              constrain
              (array mm x .== array mm y |||
               array mm x .== nonstayroom |||
               array mm y .== nonstayroom
               )
              )
           ) (prod (total z) (total z))
       )
       (shared spec)
    mapM_
       (\(j,k) ->
          mapM_
          (\(a,b) ->
            constrain
             (array mm a ./= array mm b |||
              array mm a .== nonstayroom |||
              array mm b .== nonstayroom
             )
          )
          (prod (total j) (total k))
       )
       (unshared mems)
    mapM_
     (\room_no ->
      mapM_
       (\night ->
        constrain $
         let mem = [x .== fromIntegral room_no | x<-map (array mm . (\z -> (z,night))) (mems)]
             capacity = case lookup room_no (rooms_capacity spec) of Just y -> nth night y
         in (pbAtLeast mem (capacity `monus` (least_capacity_diff spec))) &&& (pbAtMost mem capacity)
       )
       [0..((nights spec)-1)]
     )
     (map fst (rooms_capacity spec))
    additional mm
    return $ true

prod []     ys = []
prod (x:xs) ys = [ (x,y) | y<-ys ]++(prod xs ys)

nth i xs = case headMay (drop i xs) of Just j -> j

monus x y = let z = x-y
            in if z < 0 then 0 else z

parse_error_msg input = "parse error "++input
print_error_msg msg =
  do setSGR [SetColor Foreground Vivid Red]
     putStrLn msg
     setSGR [Reset]

main =
  do (input_csv:[]) <- getArgs
     fileContents <- System.IO.Strict.readFile input_csv
     (case parseCSV fileContents
      of Left _ ->
           do print_error_msg (parse_error_msg input_csv)
         Right xs ->
           do let ys = map (\x -> case headMay x
                                  of Just y -> y
                                     _ -> trace (parse_error_msg input_csv) ""
                           ) xs
                  zs = map (\x -> case readMay x
                                  of Just y -> y
                                     _ -> trace (parse_error_msg input_csv) 0
                           ) ys
              do y@(SatResult z) <- (satWith z3 . problem) zs
                 check_result <- mapM
                                 (return . (\(_,_,_,x) -> x) . check_noroom spec)
                                 (makedat_result z)
                 (if foldl' (&&) True check_result
                  then print z
                  else print_error_msg "fatal error"
                   )
       )

check_noroom spec ((mem,night),room_no) =
 if (mem,night) `elem` (nonstays spec)
 then (mem,night,room_no,(room_no == 999))
 else (mem,night,room_no,(not (room_no == 999)))

instance (Show SMTResult) where
  show = showSatResult

makedat_result :: SMTResult -> [((Int, Int), Int)]
makedat_result r@(Satisfiable _ _) =
  (sort .
    map (\(i,j) -> ((unflat . read) i,parse_z3_result j)) .
    toList .
    getModelDictionary
  )
  r

showSatResult :: SMTResult -> [Char]
showSatResult r =
  let dat = makedat_result r
  in (pr_mem dat)++
     (pr_room dat)

parse_z3_result
  = (read .
      (\((a:_):_) -> a) .
      map (splitOn " :: ") .
      splitOn " = " .
      show
    )

sep i [] = []
sep i xs = let k@((j,_):_) = take i xs
           in (j,map snd k):(sep i (drop i xs))

pr_mem :: (Show a, Show a1) => [((a, t), a1)] -> [Char]
pr_mem dat =
  concatMap
      (\((mem,_),room_no) ->
         (show mem)++(concatMap (\x -> ","++(show x)) room_no)++"\n"
      )
      (sep (nights spec) dat)

pr_room :: (Show a) => [((a, Int), Int)] -> [Char]
pr_room dat =
  (concatMap
    (\a ->
      let room_no = fst a
      in concatMap
         (\night ->
           (show room_no)++","++
           (show (nth night (snd a)))++
           (concatMap
            (\((z,y),x) -> if x==room_no && y==night then ","++(show z) else "")
            dat
           )++"\n"
         ) [0..((nights spec)-1)]
    )
    (rooms_capacity spec)
  )
