#pragma once

#include <acpi/actypes.h>

/*
 * Exception code classes
 */
#define AE_CODE_ENVIRONMENTAL           0x0000  /* General ACPICA environment */
#define AE_CODE_PROGRAMMER              0x1000  /* External ACPICA interface caller */
#define AE_CODE_ACPI_TABLES             0x2000  /* ACPI tables */
#define AE_CODE_AML                     0x3000  /* From executing AML code */
#define AE_CODE_CONTROL                 0x4000  /* Internal control codes */

#define AE_CODE_MAX                     0x4000
#define AE_CODE_MASK                    0xF000

/*
 * Macros to insert the exception code classes
 */
#define EXCEP_ENV(code)                 ((acpi_status) (code | AE_CODE_ENVIRONMENTAL))
#define EXCEP_PGM(code)                 ((acpi_status) (code | AE_CODE_PROGRAMMER))
#define EXCEP_TBL(code)                 ((acpi_status) (code | AE_CODE_ACPI_TABLES))
#define EXCEP_AML(code)                 ((acpi_status) (code | AE_CODE_AML))
#define EXCEP_CTL(code)                 ((acpi_status) (code | AE_CODE_CONTROL))

/*
 * Success is always zero, failure is non-zero
 */
#define ACPI_SUCCESS(a)                 (!(a))
#define ACPI_FAILURE(a)                 (a)

#define AE_OK                           (acpi_status) 0x0000

/*
 * Environmental exceptions
 */
#define AE_ERROR                        EXCEP_ENV (0x0001)
#define AE_NO_ACPI_TABLES               EXCEP_ENV (0x0002)
#define AE_NO_NAMESPACE                 EXCEP_ENV (0x0003)
#define AE_NO_MEMORY                    EXCEP_ENV (0x0004)
#define AE_NOT_FOUND                    EXCEP_ENV (0x0005)
#define AE_NOT_EXIST                    EXCEP_ENV (0x0006)
#define AE_ALREADY_EXISTS               EXCEP_ENV (0x0007)
#define AE_TYPE                         EXCEP_ENV (0x0008)
#define AE_NULL_OBJECT                  EXCEP_ENV (0x0009)
#define AE_NULL_ENTRY                   EXCEP_ENV (0x000A)
#define AE_BUFFER_OVERFLOW              EXCEP_ENV (0x000B)
#define AE_STACK_OVERFLOW               EXCEP_ENV (0x000C)
#define AE_STACK_UNDERFLOW              EXCEP_ENV (0x000D)
#define AE_NOT_IMPLEMENTED              EXCEP_ENV (0x000E)
#define AE_SUPPORT                      EXCEP_ENV (0x000F)
#define AE_LIMIT                        EXCEP_ENV (0x0010)
#define AE_TIME                         EXCEP_ENV (0x0011)
#define AE_ACQUIRE_DEADLOCK             EXCEP_ENV (0x0012)
#define AE_RELEASE_DEADLOCK             EXCEP_ENV (0x0013)
#define AE_NOT_ACQUIRED                 EXCEP_ENV (0x0014)
#define AE_ALREADY_ACQUIRED             EXCEP_ENV (0x0015)
#define AE_NO_HARDWARE_RESPONSE         EXCEP_ENV (0x0016)
#define AE_NO_GLOBAL_LOCK               EXCEP_ENV (0x0017)
#define AE_ABORT_METHOD                 EXCEP_ENV (0x0018)
#define AE_SAME_HANDLER                 EXCEP_ENV (0x0019)
#define AE_NO_HANDLER                   EXCEP_ENV (0x001A)
#define AE_OWNER_ID_LIMIT               EXCEP_ENV (0x001B)
#define AE_NOT_CONFIGURED               EXCEP_ENV (0x001C)
#define AE_ACCESS                       EXCEP_ENV (0x001D)
#define AE_IO_ERROR                     EXCEP_ENV (0x001E)

#define AE_CODE_ENV_MAX                 0x001E

/*
 * Programmer exceptions
 */
#define AE_BAD_PARAMETER                EXCEP_PGM (0x0001)
#define AE_BAD_CHARACTER                EXCEP_PGM (0x0002)
#define AE_BAD_PATHNAME                 EXCEP_PGM (0x0003)
#define AE_BAD_DATA                     EXCEP_PGM (0x0004)
#define AE_BAD_HEX_CONSTANT             EXCEP_PGM (0x0005)
#define AE_BAD_OCTAL_CONSTANT           EXCEP_PGM (0x0006)
#define AE_BAD_DECIMAL_CONSTANT         EXCEP_PGM (0x0007)
#define AE_MISSING_ARGUMENTS            EXCEP_PGM (0x0008)
#define AE_BAD_ADDRESS                  EXCEP_PGM (0x0009)

#define AE_CODE_PGM_MAX                 0x0009

/*
 * Acpi table exceptions
 */
#define AE_BAD_SIGNATURE                EXCEP_TBL (0x0001)
#define AE_BAD_HEADER                   EXCEP_TBL (0x0002)
#define AE_BAD_CHECKSUM                 EXCEP_TBL (0x0003)
#define AE_BAD_VALUE                    EXCEP_TBL (0x0004)
#define AE_INVALID_TABLE_LENGTH         EXCEP_TBL (0x0005)

#define AE_CODE_TBL_MAX                 0x0005
