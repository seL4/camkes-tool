create table if not exists input (
    output integer not null references output (id),
    path text not null,
    sha256 text not null);
