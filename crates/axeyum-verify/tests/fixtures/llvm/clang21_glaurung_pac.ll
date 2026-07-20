; ModuleID = 'tests/fixtures/android/pac.c'
source_filename = "tests/fixtures/android/pac.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local range(i32 -2147483647, -2147483648) i32 @leaf(i32 noundef %0) #0 {
  %2 = mul nsw i32 %0, %0
  %3 = add nuw nsw i32 %2, 1
  ret i32 %3
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local noundef nonnull ptr @pick(i32 noundef %0) local_unnamed_addr #0 {
  ret ptr @leaf
}

; Function Attrs: nofree norecurse nosync nounwind memory(none) uwtable
define dso_local i32 @compute(i32 noundef %0) local_unnamed_addr #1 {
  %2 = icmp sgt i32 %0, 0
  br i1 %2, label %5, label %3

3:                                                ; preds = %5, %1
  %4 = phi i32 [ 0, %1 ], [ %9, %5 ]
  ret i32 %4

5:                                                ; preds = %1, %5
  %6 = phi i32 [ %10, %5 ], [ 0, %1 ]
  %7 = phi i32 [ %9, %5 ], [ 0, %1 ]
  %8 = tail call i32 @leaf(i32 noundef %6)
  %9 = add nsw i32 %8, %7
  %10 = add nuw nsw i32 %6, 1
  %11 = icmp eq i32 %10, %0
  br i1 %11, label %3, label %5, !llvm.loop !5
}

; Function Attrs: nofree norecurse nosync nounwind memory(none) uwtable
define dso_local range(i32 0, 256) i32 @main(i32 noundef %0, ptr noundef readnone captures(none) %1) local_unnamed_addr #1 {
  %3 = icmp sgt i32 %0, 0
  br i1 %3, label %4, label %13

4:                                                ; preds = %2, %4
  %5 = phi i32 [ %9, %4 ], [ 0, %2 ]
  %6 = phi i32 [ %8, %4 ], [ 0, %2 ]
  %7 = tail call i32 @leaf(i32 noundef %5)
  %8 = add nsw i32 %7, %6
  %9 = add nuw nsw i32 %5, 1
  %10 = icmp eq i32 %9, %0
  br i1 %10, label %11, label %4, !llvm.loop !5

11:                                               ; preds = %4
  %12 = and i32 %8, 255
  br label %13

13:                                               ; preds = %11, %2
  %14 = phi i32 [ 0, %2 ], [ %12, %11 ]
  ret i32 %14
}

attributes #0 = { mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nofree norecurse nosync nounwind memory(none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

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
