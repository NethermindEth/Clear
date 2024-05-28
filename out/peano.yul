object "Peano" {
    code {
    }
    object "Peano_deployed" {
        code {
            function addk(x, k) -> y
            {
                for {} 1 {k := sub(k, 1)} {
                    if eq(k, 0)
                    {
                        break
                    }
                    x := add(x, 1)
                }
                y := x
            }
            function mulk(x, k) -> y
            {
                let y := 0
                for {} 1 {k := sub(k, 1)} {
                    if eq(k, 0)
                    {
                        break
                    }
                    y := addk(y, x)
                }
            }
            function expk(x, k) -> y
            {
                let y := 1
                for {} 1 {k := sub(k, 1)} {
                    if eq(k, 0)
                    {
                        break
                    }
                    y := mulk(y, x)
                }
            }
        }
        data ".metadata" hex"a264697066735822122067106f228801aa898d329c27cddd7517e178492c852b664d920e4c3c137b297464736f6c63430008130033"
    }
}