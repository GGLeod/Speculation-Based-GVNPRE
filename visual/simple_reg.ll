; ModuleID = 'simple_reg.bc'
source_filename = "../test/simple.cpp"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline norecurse nounwind uwtable mustprogress
define dso_local i32 @main() #0 {
entry:
  %rem = srem i32 1, 100
  %cmp = icmp eq i32 %rem, 1
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %add = add nsw i32 0, 1
  br label %if.end

if.else:                                          ; preds = %entry
  %add1 = add nsw i32 1, 2
  %add2 = add nsw i32 0, %add1
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %c.0 = phi i32 [ %add, %if.then ], [ %add2, %if.else ]
  %rem3 = srem i32 2, 200
  %cmp4 = icmp eq i32 %rem3, 1
  br i1 %cmp4, label %if.then5, label %if.else7

if.then5:                                         ; preds = %if.end
  %sub = sub nsw i32 %c.0, 2
  %add6 = add nsw i32 %sub, 1
  br label %if.end11

if.else7:                                         ; preds = %if.end
  %add9 = add nsw i32 1, 2
  %add10 = add nsw i32 %c.0, %add9
  br label %if.end11

if.end11:                                         ; preds = %if.else7, %if.then5
  ret i32 0
}

attributes #0 = { noinline norecurse nounwind uwtable mustprogress "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git fed41342a82f5a3a9201819a82bf7a48313e296b)"}
