#pragma once

/* VGA data register ports */
#define VGA_CRT_DC      0x3D5   /* CRT Controller Data Register - color emulation */
#define VGA_CRT_DM      0x3B5   /* CRT Controller Data Register - mono emulation */
#define VGA_ATT_R       0x3C1   /* Attribute Controller Data Read Register */
#define VGA_ATT_W       0x3C0   /* Attribute Controller Data Write Register */
#define VGA_GFX_D       0x3CF   /* Graphics Controller Data Register */
#define VGA_SEQ_D       0x3C5   /* Sequencer Data Register */
#define VGA_MIS_R       0x3CC   /* Misc Output Read Register */
#define VGA_MIS_W       0x3C2   /* Misc Output Write Register */
#define VGA_FTC_R       0x3CA   /* Feature Control Read Register */
#define VGA_IS1_RC      0x3DA   /* Input Status Register 1 - color emulation */
#define VGA_IS1_RM      0x3BA   /* Input Status Register 1 - mono emulation */
#define VGA_PEL_D       0x3C9   /* PEL Data Register */
#define VGA_PEL_MSK     0x3C6   /* PEL mask register */

/* VGA index register ports */
#define VGA_CRT_IC      0x3D4   /* CRT Controller Index - color emulation */
#define VGA_CRT_IM      0x3B4   /* CRT Controller Index - mono emulation */
#define VGA_ATT_IW      0x3C0   /* Attribute Controller Index & Data Write Register */
#define VGA_GFX_I       0x3CE   /* Graphics Controller Index */
#define VGA_SEQ_I       0x3C4   /* Sequencer Index */
#define VGA_PEL_IW      0x3C8   /* PEL Write Index */
#define VGA_PEL_IR      0x3C7   /* PEL Read Index */

/* VGA CRT controller register indices */
#define VGA_CRTC_H_TOTAL        0
#define VGA_CRTC_H_DISP         1
#define VGA_CRTC_H_BLANK_START  2
#define VGA_CRTC_H_BLANK_END    3
#define VGA_CRTC_H_SYNC_START   4
#define VGA_CRTC_H_SYNC_END     5
#define VGA_CRTC_V_TOTAL        6
#define VGA_CRTC_OVERFLOW       7
#define VGA_CRTC_PRESET_ROW     8
#define VGA_CRTC_MAX_SCAN       9
#define VGA_CRTC_CURSOR_START   0x0A
#define VGA_CRTC_CURSOR_END     0x0B
#define VGA_CRTC_START_HI       0x0C
#define VGA_CRTC_START_LO       0x0D
#define VGA_CRTC_CURSOR_HI      0x0E
#define VGA_CRTC_CURSOR_LO      0x0F
#define VGA_CRTC_V_SYNC_START   0x10
#define VGA_CRTC_V_SYNC_END     0x11
#define VGA_CRTC_V_DISP_END     0x12
#define VGA_CRTC_OFFSET         0x13
#define VGA_CRTC_UNDERLINE      0x14
#define VGA_CRTC_V_BLANK_START  0x15
#define VGA_CRTC_V_BLANK_END    0x16
#define VGA_CRTC_MODE           0x17
#define VGA_CRTC_LINE_COMPARE   0x18
#define VGA_CRTC_REGS           VGA_CRT_C
