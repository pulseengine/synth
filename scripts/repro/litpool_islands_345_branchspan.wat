(module
  ;; RED-FIRST for the v0.72 cold review's FINDING 1.
  ;; Same shape as litpool_islands_345.wat with ONE addition: a forward
  ;; `br_if` that SPANS the point where the inline island is inserted.
  ;; The shipped fixture has zero control-flow ops, so the oracle cannot
  ;; see this class at all.
  (memory 1)
  (data (i32.const 1024) "islands-345")
  (func $big (export "big") (param i32) (result i32) (local i32) (local i64)
    (block
    i32.const 1024
    i32.load
    local.set 1
    local.get 0
    br_if 0
    local.get 2
    i64.const 3
    i64.mul
    local.set 2
    local.get 2
    i64.const 4
    i64.mul
    local.set 2
    local.get 2
    i64.const 5
    i64.mul
    local.set 2
    local.get 2
    i64.const 6
    i64.mul
    local.set 2
    local.get 2
    i64.const 7
    i64.mul
    local.set 2
    local.get 2
    i64.const 8
    i64.mul
    local.set 2
    local.get 2
    i64.const 9
    i64.mul
    local.set 2
    local.get 2
    i64.const 10
    i64.mul
    local.set 2
    local.get 2
    i64.const 11
    i64.mul
    local.set 2
    local.get 2
    i64.const 12
    i64.mul
    local.set 2
    local.get 2
    i64.const 13
    i64.mul
    local.set 2
    local.get 2
    i64.const 14
    i64.mul
    local.set 2
    local.get 2
    i64.const 15
    i64.mul
    local.set 2
    local.get 2
    i64.const 16
    i64.mul
    local.set 2
    local.get 2
    i64.const 17
    i64.mul
    local.set 2
    local.get 2
    i64.const 18
    i64.mul
    local.set 2
    local.get 2
    i64.const 19
    i64.mul
    local.set 2
    local.get 2
    i64.const 20
    i64.mul
    local.set 2
    local.get 2
    i64.const 21
    i64.mul
    local.set 2
    local.get 2
    i64.const 22
    i64.mul
    local.set 2
    local.get 2
    i64.const 23
    i64.mul
    local.set 2
    local.get 2
    i64.const 24
    i64.mul
    local.set 2
    local.get 2
    i64.const 25
    i64.mul
    local.set 2
    local.get 2
    i64.const 26
    i64.mul
    local.set 2
    local.get 2
    i64.const 27
    i64.mul
    local.set 2
    local.get 2
    i64.const 28
    i64.mul
    local.set 2
    local.get 2
    i64.const 29
    i64.mul
    local.set 2
    local.get 2
    i64.const 30
    i64.mul
    local.set 2
    local.get 2
    i64.const 31
    i64.mul
    local.set 2
    local.get 2
    i64.const 32
    i64.mul
    local.set 2
    local.get 2
    i64.const 33
    i64.mul
    local.set 2
    local.get 2
    i64.const 34
    i64.mul
    local.set 2
    local.get 2
    i64.const 35
    i64.mul
    local.set 2
    local.get 2
    i64.const 36
    i64.mul
    local.set 2
    local.get 2
    i64.const 37
    i64.mul
    local.set 2
    local.get 2
    i64.const 38
    i64.mul
    local.set 2
    local.get 2
    i64.const 39
    i64.mul
    local.set 2
    local.get 2
    i64.const 40
    i64.mul
    local.set 2
    local.get 2
    i64.const 41
    i64.mul
    local.set 2
    local.get 2
    i64.const 42
    i64.mul
    local.set 2
    local.get 2
    i64.const 43
    i64.mul
    local.set 2
    local.get 2
    i64.const 44
    i64.mul
    local.set 2
    local.get 2
    i64.const 45
    i64.mul
    local.set 2
    local.get 2
    i64.const 46
    i64.mul
    local.set 2
    local.get 2
    i64.const 47
    i64.mul
    local.set 2
    local.get 2
    i64.const 48
    i64.mul
    local.set 2
    local.get 2
    i64.const 49
    i64.mul
    local.set 2
    local.get 2
    i64.const 50
    i64.mul
    local.set 2
    local.get 2
    i64.const 51
    i64.mul
    local.set 2
    local.get 2
    i64.const 52
    i64.mul
    local.set 2
    local.get 2
    i64.const 53
    i64.mul
    local.set 2
    local.get 2
    i64.const 54
    i64.mul
    local.set 2
    local.get 2
    i64.const 55
    i64.mul
    local.set 2
    local.get 2
    i64.const 56
    i64.mul
    local.set 2
    local.get 2
    i64.const 57
    i64.mul
    local.set 2
    local.get 2
    i64.const 58
    i64.mul
    local.set 2
    local.get 2
    i64.const 59
    i64.mul
    local.set 2
    local.get 2
    i64.const 60
    i64.mul
    local.set 2
    local.get 2
    i64.const 61
    i64.mul
    local.set 2
    local.get 2
    i64.const 62
    i64.mul
    local.set 2
    local.get 2
    i64.const 63
    i64.mul
    local.set 2
    local.get 2
    i64.const 3
    i64.mul
    local.set 2
    local.get 2
    i64.const 4
    i64.mul
    local.set 2
    local.get 2
    i64.const 5
    i64.mul
    local.set 2
    local.get 2
    i64.const 6
    i64.mul
    local.set 2
    local.get 2
    i64.const 7
    i64.mul
    local.set 2
    local.get 2
    i64.const 8
    i64.mul
    local.set 2
    local.get 2
    i64.const 9
    i64.mul
    local.set 2
    local.get 2
    i64.const 10
    i64.mul
    local.set 2
    local.get 2
    i64.const 11
    i64.mul
    local.set 2
    local.get 2
    i64.const 12
    i64.mul
    local.set 2
    local.get 2
    i64.const 13
    i64.mul
    local.set 2
    local.get 2
    i64.const 14
    i64.mul
    local.set 2
    local.get 2
    i64.const 15
    i64.mul
    local.set 2
    local.get 2
    i64.const 16
    i64.mul
    local.set 2
    local.get 2
    i64.const 17
    i64.mul
    local.set 2
    local.get 2
    i64.const 18
    i64.mul
    local.set 2
    local.get 2
    i64.const 19
    i64.mul
    local.set 2
    local.get 2
    i64.const 20
    i64.mul
    local.set 2
    local.get 2
    i64.const 21
    i64.mul
    local.set 2
    local.get 2
    i64.const 22
    i64.mul
    local.set 2
    local.get 2
    i64.const 23
    i64.mul
    local.set 2
    local.get 2
    i64.const 24
    i64.mul
    local.set 2
    local.get 2
    i64.const 25
    i64.mul
    local.set 2
    local.get 2
    i64.const 26
    i64.mul
    local.set 2
    local.get 2
    i64.const 27
    i64.mul
    local.set 2
    local.get 2
    i64.const 28
    i64.mul
    local.set 2
    local.get 2
    i64.const 29
    i64.mul
    local.set 2
    local.get 2
    i64.const 30
    i64.mul
    local.set 2
    local.get 2
    i64.const 31
    i64.mul
    local.set 2
    local.get 2
    i64.const 32
    i64.mul
    local.set 2
    local.get 2
    i64.const 33
    i64.mul
    local.set 2
    local.get 2
    i64.const 34
    i64.mul
    local.set 2
    local.get 2
    i64.const 35
    i64.mul
    local.set 2
    local.get 2
    i64.const 36
    i64.mul
    local.set 2
    local.get 2
    i64.const 37
    i64.mul
    local.set 2
    local.get 2
    i64.const 38
    i64.mul
    local.set 2
    local.get 2
    i64.const 39
    i64.mul
    local.set 2
    local.get 2
    i64.const 40
    i64.mul
    local.set 2
    local.get 2
    i64.const 41
    i64.mul
    local.set 2
    local.get 2
    i64.const 42
    i64.mul
    local.set 2
    local.get 2
    i64.const 43
    i64.mul
    local.set 2
    local.get 2
    i64.const 44
    i64.mul
    local.set 2
    local.get 2
    i64.const 45
    i64.mul
    local.set 2
    local.get 2
    i64.const 46
    i64.mul
    local.set 2
    local.get 2
    i64.const 47
    i64.mul
    local.set 2
    local.get 2
    i64.const 48
    i64.mul
    local.set 2
    local.get 2
    i64.const 49
    i64.mul
    local.set 2
    local.get 2
    i64.const 50
    i64.mul
    local.set 2
    local.get 2
    i64.const 51
    i64.mul
    local.set 2
    local.get 2
    i64.const 52
    i64.mul
    local.set 2
    local.get 2
    i64.const 53
    i64.mul
    local.set 2
    local.get 2
    i64.const 54
    i64.mul
    local.set 2
    local.get 2
    i64.const 55
    i64.mul
    local.set 2
    local.get 2
    i64.const 56
    i64.mul
    local.set 2
    local.get 2
    i64.const 57
    i64.mul
    local.set 2
    local.get 2
    i64.const 58
    i64.mul
    local.set 2
    local.get 2
    i64.const 59
    i64.mul
    local.set 2
    local.get 2
    i64.const 60
    i64.mul
    local.set 2
    local.get 2
    i64.const 61
    i64.mul
    local.set 2
    local.get 2
    i64.const 62
    i64.mul
    local.set 2
    local.get 2
    i64.const 63
    i64.mul
    local.set 2
    local.get 2
    i64.const 3
    i64.mul
    local.set 2
    local.get 2
    i64.const 4
    i64.mul
    local.set 2
    local.get 2
    i64.const 5
    i64.mul
    local.set 2
    local.get 2
    i64.const 6
    i64.mul
    local.set 2
    local.get 2
    i64.const 7
    i64.mul
    local.set 2
    local.get 2
    i64.const 8
    i64.mul
    local.set 2
    local.get 2
    i64.const 9
    i64.mul
    local.set 2
    local.get 2
    i64.const 10
    i64.mul
    local.set 2
    local.get 2
    i64.const 11
    i64.mul
    local.set 2
    local.get 2
    i64.const 12
    i64.mul
    local.set 2
    local.get 2
    i64.const 13
    i64.mul
    local.set 2
    local.get 2
    i64.const 14
    i64.mul
    local.set 2
    local.get 2
    i64.const 15
    i64.mul
    local.set 2
    local.get 2
    i64.const 16
    i64.mul
    local.set 2
    local.get 2
    i64.const 17
    i64.mul
    local.set 2
    local.get 2
    i64.const 18
    i64.mul
    local.set 2
    local.get 2
    i64.const 19
    i64.mul
    local.set 2
    local.get 2
    i64.const 20
    i64.mul
    local.set 2
    local.get 2
    i64.const 21
    i64.mul
    local.set 2
    local.get 2
    i64.const 22
    i64.mul
    local.set 2
    local.get 2
    i64.const 23
    i64.mul
    local.set 2
    local.get 2
    i64.const 24
    i64.mul
    local.set 2
    local.get 2
    i64.const 25
    i64.mul
    local.set 2
    local.get 2
    i64.const 26
    i64.mul
    local.set 2
    local.get 2
    i64.const 27
    i64.mul
    local.set 2
    local.get 2
    i64.const 28
    i64.mul
    local.set 2
    local.get 2
    i64.const 29
    i64.mul
    local.set 2
    local.get 2
    i64.const 30
    i64.mul
    local.set 2
    local.get 2
    i64.const 31
    i64.mul
    local.set 2
    local.get 2
    i64.const 32
    i64.mul
    local.set 2
    local.get 2
    i64.const 33
    i64.mul
    local.set 2
    local.get 2
    i64.const 34
    i64.mul
    local.set 2
    local.get 2
    i64.const 35
    i64.mul
    local.set 2
    local.get 2
    i64.const 36
    i64.mul
    local.set 2
    local.get 2
    i64.const 37
    i64.mul
    local.set 2
    local.get 2
    i64.const 38
    i64.mul
    local.set 2
    local.get 2
    i64.const 39
    i64.mul
    local.set 2
    local.get 2
    i64.const 40
    i64.mul
    local.set 2
    local.get 2
    i64.const 41
    i64.mul
    local.set 2
    local.get 2
    i64.const 42
    i64.mul
    local.set 2
    local.get 2
    i64.const 43
    i64.mul
    local.set 2
    local.get 2
    i64.const 44
    i64.mul
    local.set 2
    local.get 2
    i64.const 45
    i64.mul
    local.set 2
    local.get 2
    i64.const 46
    i64.mul
    local.set 2
    local.get 2
    i64.const 47
    i64.mul
    local.set 2
    local.get 2
    i64.const 48
    i64.mul
    local.set 2
    local.get 2
    i64.const 49
    i64.mul
    local.set 2
    local.get 2
    i64.const 50
    i64.mul
    local.set 2
    local.get 2
    i64.const 51
    i64.mul
    local.set 2
    local.get 2
    i64.const 52
    i64.mul
    local.set 2
    local.get 2
    i64.const 53
    i64.mul
    local.set 2
    local.get 2
    i64.const 54
    i64.mul
    local.set 2
    local.get 2
    i64.const 55
    i64.mul
    local.set 2
    local.get 2
    i64.const 56
    i64.mul
    local.set 2
    local.get 2
    i64.const 57
    i64.mul
    local.set 2
    local.get 2
    i64.const 58
    i64.mul
    local.set 2
    local.get 2
    i64.const 59
    i64.mul
    local.set 2
    local.get 2
    i64.const 60
    i64.mul
    local.set 2
    local.get 2
    i64.const 61
    i64.mul
    local.set 2
    local.get 2
    i64.const 62
    i64.mul
    local.set 2
    local.get 2
    i64.const 63
    i64.mul
    local.set 2
    local.get 2
    i64.const 3
    i64.mul
    local.set 2
    local.get 2
    i64.const 4
    i64.mul
    local.set 2
    local.get 2
    i64.const 5
    i64.mul
    local.set 2
    local.get 2
    i64.const 6
    i64.mul
    local.set 2
    local.get 2
    i64.const 7
    i64.mul
    local.set 2
    local.get 2
    i64.const 8
    i64.mul
    local.set 2
    local.get 2
    i64.const 9
    i64.mul
    local.set 2
    local.get 2
    i64.const 10
    i64.mul
    local.set 2
    local.get 2
    i64.const 11
    i64.mul
    local.set 2
    local.get 2
    i64.const 12
    i64.mul
    local.set 2
    local.get 2
    i64.const 13
    i64.mul
    local.set 2
    local.get 2
    i64.const 14
    i64.mul
    local.set 2
    local.get 2
    i64.const 15
    i64.mul
    local.set 2
    local.get 2
    i64.const 16
    i64.mul
    local.set 2
    local.get 2
    i64.const 17
    i64.mul
    local.set 2
    local.get 2
    i64.const 18
    i64.mul
    local.set 2
    local.get 2
    i64.const 19
    i64.mul
    local.set 2
    local.get 2
    i64.const 20
    i64.mul
    local.set 2
    local.get 2
    i64.const 21
    i64.mul
    local.set 2
    local.get 2
    i64.const 22
    i64.mul
    local.set 2
    local.get 2
    i64.const 23
    i64.mul
    local.set 2
    local.get 2
    i64.const 24
    i64.mul
    local.set 2
    local.get 2
    i64.const 25
    i64.mul
    local.set 2
    local.get 2
    i64.const 26
    i64.mul
    local.set 2
    local.get 2
    i64.const 27
    i64.mul
    local.set 2
    local.get 2
    i64.const 28
    i64.mul
    local.set 2
    local.get 2
    i64.const 29
    i64.mul
    local.set 2
    local.get 2
    i64.const 30
    i64.mul
    local.set 2
    local.get 2
    i64.const 31
    i64.mul
    local.set 2
    local.get 2
    i64.const 32
    i64.mul
    local.set 2
    local.get 2
    i64.const 33
    i64.mul
    local.set 2
    local.get 2
    i64.const 34
    i64.mul
    local.set 2
    local.get 2
    i64.const 35
    i64.mul
    local.set 2
    local.get 2
    i64.const 36
    i64.mul
    local.set 2
    local.get 2
    i64.const 37
    i64.mul
    local.set 2
    local.get 2
    i64.const 38
    i64.mul
    local.set 2
    local.get 2
    i64.const 39
    i64.mul
    local.set 2
    local.get 2
    i64.const 40
    i64.mul
    local.set 2
    local.get 2
    i64.const 41
    i64.mul
    local.set 2
    local.get 2
    i64.const 42
    i64.mul
    local.set 2
    local.get 2
    i64.const 43
    i64.mul
    local.set 2
    local.get 2
    i64.const 44
    i64.mul
    local.set 2
    local.get 2
    i64.const 45
    i64.mul
    local.set 2
    local.get 2
    i64.const 46
    i64.mul
    local.set 2
    local.get 2
    i64.const 47
    i64.mul
    local.set 2
    local.get 2
    i64.const 48
    i64.mul
    local.set 2
    local.get 2
    i64.const 49
    i64.mul
    local.set 2
    local.get 2
    i64.const 50
    i64.mul
    local.set 2
    local.get 2
    i64.const 51
    i64.mul
    local.set 2
    local.get 2
    i64.const 52
    i64.mul
    local.set 2
    local.get 2
    i64.const 53
    i64.mul
    local.set 2
    local.get 2
    i64.const 54
    i64.mul
    local.set 2
    local.get 2
    i64.const 55
    i64.mul
    local.set 2
    local.get 2
    i64.const 56
    i64.mul
    local.set 2
    local.get 2
    i64.const 57
    i64.mul
    local.set 2
    local.get 2
    i64.const 58
    i64.mul
    local.set 2
    local.get 2
    i64.const 59
    i64.mul
    local.set 2
    local.get 2
    i64.const 60
    i64.mul
    local.set 2
    local.get 2
    i64.const 61
    i64.mul
    local.set 2
    local.get 2
    i64.const 62
    i64.mul
    local.set 2
    local.get 2
    i64.const 63
    i64.mul
    local.set 2
    local.get 2
    i64.const 3
    i64.mul
    local.set 2
    local.get 2
    i64.const 4
    i64.mul
    local.set 2
    local.get 2
    i64.const 5
    i64.mul
    local.set 2
    local.get 2
    i64.const 6
    i64.mul
    local.set 2
    local.get 2
    i64.const 7
    i64.mul
    local.set 2
    local.get 2
    i64.const 8
    i64.mul
    local.set 2
    local.get 2
    i64.const 9
    i64.mul
    local.set 2
    local.get 2
    i64.const 10
    i64.mul
    local.set 2
    local.get 2
    i64.const 11
    i64.mul
    local.set 2
    local.get 2
    i64.const 12
    i64.mul
    local.set 2
    local.get 2
    i64.const 13
    i64.mul
    local.set 2
    local.get 2
    i64.const 14
    i64.mul
    local.set 2
    local.get 2
    i64.const 15
    i64.mul
    local.set 2
    local.get 2
    i64.const 16
    i64.mul
    local.set 2
    local.get 2
    i64.const 17
    i64.mul
    local.set 2
    local.get 2
    i64.const 18
    i64.mul
    local.set 2
    )
    local.get 1
    local.get 2
    i32.wrap_i64
    i32.add
  )
)
