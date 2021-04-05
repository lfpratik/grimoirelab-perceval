import logging
from logging.handlers import SMTPHandler


"""
Thanks to: https://stackoverflow.com/questions/9235997/is-there-a-way-how-to-configure-smtphandler-in-python-to-do-more-advanced-stuff/20801330
"""


class SDSSMTPHandler(SMTPHandler):

    @classmethod
    def get_log_level(cls, level=None):
        if level == 10:
            return logging.DEBUG
        elif level == 20:
            return logging.INFO
        elif level == 30:
            return logging.WARNING
        elif level == 40:
            return logging.ERROR
        else:
            return logging.ERROR

    @classmethod
    def get_log_format(cls):
        format = logging.Formatter(
            'Time:- %(asctime)s\n'
            'File:- %(filename)s\n'
            'Module:- %(module)s\n'
            'Function:- %(funcName)s\n'
            'Line:- %(lineno)d\n'
            'Level:- %(levelname)s\n'
            'Message: %(message)s\n'
            'Traceback: %(exc_text)s\n')
        return format

    def getSubject(self, record):
        return 'SDS | Error from {0}'.format(record.module)

    def emit(self, record):
        """
        Overwrite the logging.handlers.SMTPHandler.emit function with SMTP_SSL.
        Emit a record.
        Format the record and send it to the specified addressees.
        """
        try:
            import smtplib
            from email.utils import formatdate
            port = self.mailport
            if not port:
                port = smtplib.SMTP_PORT
            smtp = smtplib.SMTP_SSL(self.mailhost, port, timeout=5.0)
            msg = self.format(record)
            msg = "From: %s\r\nTo: %s\r\nSubject: %s\r\nDate: %s\r\n\r\n%s" % (
            self.fromaddr, ", ".join(self.toaddrs), self.getSubject(record),
            formatdate(), msg)
            if self.username:
                smtp.ehlo()
                smtp.login(self.username, self.password)
            smtp.sendmail(self.fromaddr, self.toaddrs, msg)
            smtp.quit()
        except (KeyboardInterrupt, SystemExit):
            raise
        except Exception as e:
            self.handleError(record)


def get_smtp_handler():
    return SDSSMTPHandler(
        mailhost=('smtp.gmail.com', 465),
        fromaddr='dev.analytics.error.bot@gmail.com',
        toaddrs=['pratikk@proximabiz.com', 'sgupta@linuxfoundation.org',
                 'fghiasy@linuxfoundation.org'],
        subject='SDS Error - log',
        credentials=('dev.analytics.error.bot@gmail.com', 'Mobile@311!'),
        timeout=5.0,
        secure=None
    )
