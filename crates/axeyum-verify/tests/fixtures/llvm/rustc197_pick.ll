; ModuleID = 'rust_out.13ab2567a5361cb2-cgu.0'
source_filename = "rust_out.13ab2567a5361cb2-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef i32 @pick(i1 noundef zeroext %c, i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %a.b = select i1 %c, i32 %a, i32 %b
  ret i32 %a.b
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.97.0-nightly (f53b654a8 2026-04-30)"}
