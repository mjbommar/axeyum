define dso_local zeroext range(i8 0, 101) i8 @capsum8(i8 noundef zeroext %0) local_unnamed_addr {
  %2 = icmp eq i8 %0, 0
  br i1 %2, label %3, label %5

3:
  %4 = phi i8 [ 0, %1 ], [ %9, %5 ]
  ret i8 %4

5:
  %6 = phi i8 [ %10, %5 ], [ 0, %1 ]
  %7 = phi i8 [ %9, %5 ], [ 0, %1 ]
  %8 = tail call i8 @llvm.umin.i8(i8 %7, i8 99)
  %9 = add nuw nsw i8 %8, 1
  %10 = add nuw i8 %6, 1
  %11 = icmp eq i8 %10, %0
  br i1 %11, label %3, label %5
}
