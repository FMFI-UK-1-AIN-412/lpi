#! /usr/bin/env python3
from dataclasses import dataclass


@dataclass
class Riesenie:
    otec: str
    matka: str
    syn: str
    dcera: str


class Rodinka:
    def vyries(self) -> Riesenie:
        return Riesenie(otec='', matka='', syn='', dcera='')
