let v0 = vector(42)
  in let v1 = vector(v0, v0)
    in let v2 = vector(v1, v1, v1, v1)
      in let v3 = vector(v2, v2, v2, v2, v2, v2, v2, v2)
        in let v4 = vector(v3, v3, v3, v3, v3, v3, v3, v3, v3, v3, v3, v3, v3, v3, v3, v3)
          in vectorRef(vectorRef(vectorRef(vectorRef(vectorRef(v4, 4), 3), 2), 1), 0)
