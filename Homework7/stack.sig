(defsig Stack
  (sig (type (Stack a))
       (val push (a -> (Stack a)-> (Stack a)))
       (val emptySt (Stack a))
       (val pop ((Stack a)-> (a . (Stack a))))))
