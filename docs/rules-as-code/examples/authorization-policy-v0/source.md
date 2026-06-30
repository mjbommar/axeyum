# Source Policy

This is an example policy written for testing. It is not legal advice and does
not describe a production authorization system.

## Rule 2a Tenants

Every user and every resource has exactly one tenant. A request may be allowed
only when the user's tenant equals the resource's tenant.

## Rule 2b Role Permits

The `analyst` role may read same-tenant resources. In policy version 2, the
`analyst` role may also export same-tenant resources. The `admin` role may read
and export same-tenant resources. No role may delete resources in this example
policy.

## Rule 2c Explicit Deny

An explicit deny entry overrides any role permit.

## Rule 2d Admin Override

The `admin` role can use the ordinary read/export permits without needing the
`analyst` role. The admin override does not bypass tenant isolation and does
not override an explicit deny.

## Rule 2e Version Change

Policy version 1 denies analyst export. Policy version 2 allows analyst export
for same-tenant resources when no explicit deny applies. No other request shape
is intended to change between version 1 and version 2.
