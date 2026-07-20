; ModuleID = '-'
source_filename = "-"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind memory(none) uwtable
define dso_local zeroext range(i8 0, 101) i8 @capdiv(i8 noundef zeroext %0, i8 noundef zeroext %1) local_unnamed_addr #0 {
  %3 = icmp eq i8 %0, 0
  br i1 %3, label %4, label %6

4:                                                ; preds = %15, %2
  %5 = phi i8 [ 0, %2 ], [ %16, %15 ]
  ret i8 %5

6:                                                ; preds = %2, %15
  %7 = phi i8 [ %16, %15 ], [ 0, %2 ]
  %8 = phi i8 [ %17, %15 ], [ 0, %2 ]
  %9 = and i8 %8, 1
  %10 = icmp eq i8 %9, 0
  br i1 %10, label %15, label %11

11:                                               ; preds = %6
  %12 = udiv i8 %8, %1
  %13 = add i8 %12, %7
  %14 = tail call i8 @llvm.umin.i8(i8 %13, i8 100)
  br label %15

15:                                               ; preds = %6, %11
  %16 = phi i8 [ %14, %11 ], [ %7, %6 ]
  %17 = add nuw i8 %8, 1
  %18 = icmp eq i8 %17, %0
  br i1 %18, label %4, label %6, !llvm.loop !5
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i8 @llvm.umin.i8(i8, i8) #1

attributes #0 = { nofree norecurse nosync nounwind memory(none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{!"Ubuntu clang version 21.1.8 (6ubuntu1)"}
!5 = distinct !{!5, !6, !7}
!6 = !{!"llvm.loop.mustprogress"}
!7 = !{!"llvm.loop.unroll.disable"}
